#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Livraria — Controle de Estoque
==============================
//pull request test
Aplicação desktop (Tkinter + SQLite, só biblioteca padrão, Python 3.9+).

Telas
-----
1. TelaMenu        Login (usuário/senha) e acesso a Cadastrar, Movimentar e Consultar.
2. TelaOperacao    Cadastro de livro e movimentação (Entrada/Saída) com validação.
3. TelaResultados  Mensagem de sucesso/erro, tabela de estoque, pesquisa e alertas.

Como executar
-------------
    python estoque_livraria.py

Usuários criados no primeiro uso (TROQUE as senhas antes de usar de verdade):
    admin   / admin123    -> perfil administrador (cadastra, movimenta, consulta)
    estoque / estoque123  -> perfil estoquista    (movimenta, consulta)

Criar ou redefinir um usuário (a senha é pedida sem aparecer na tela):
    python estoque_livraria.py --criar-usuario NOME admin
    python estoque_livraria.py --criar-usuario NOME estoquista

Atalhos de teclado: Tab/Shift+Tab navegam, Enter confirma, Espaço aciona botões,
Esc volta ao menu.
"""

from __future__ import annotations

import getpass
import hashlib
import hmac
import logging
import math
import os
import re
import sqlite3
import sys
import time
import tkinter as tk
import unicodedata
from datetime import datetime
from decimal import Decimal
from pathlib import Path
from tkinter import messagebox, ttk

# --------------------------------------------------------------------------- #
# Configuração
# --------------------------------------------------------------------------- #
BASE = Path(__file__).resolve().parent
DB_PATH = BASE / "livraria.db"
LOG_PATH = BASE / "erros.log"

ESTOQUE_BAIXO = 3          # até este número de exemplares o livro entra em alerta
MAX_TENTATIVAS = 5         # tentativas de login antes do bloqueio temporário
BLOQUEIO_SEGUNDOS = 30
LIMITE_QTD = 100000        # quantidade máxima por operação
ITERACOES_HASH = 200_000
MIN_ALVO = 44              # área mínima de toque/clique, em pixels

# Cores — todas as combinações de texto/fundo têm contraste >= 4,5:1
COR = {
    "fundo": "#FFFFFF",
    "fundo_alt": "#F3F4F6",
    "campo": "#FFFFFF",
    "texto": "#1A1A1A",
    "texto_suave": "#404040",
    "primaria": "#0B3D91",
    "primaria_ativa": "#082B66",
    "primaria_texto": "#FFFFFF",
    "secundaria": "#E5E7EB",
    "secundaria_ativa": "#D1D5DB",
    "selecao": "#BBD3FF",
    "borda": "#767676",
    "foco": "#C2410C",             # anel de foco bem visível
    "desabilitado_bg": "#D9D9D9",
    "desabilitado_texto": "#595959",
    "erro_fg": "#8A1111",
}

# tipo -> (símbolo, rótulo, fundo, texto): o símbolo e o rótulo garantem que a cor
# nunca seja o único meio de transmitir a informação.
ALERTAS = {
    "ok": ("✔", "Sucesso", "#E6F4EA", "#0B5D1E"),
    "erro": ("✖", "Erro", "#FDECEA", "#8A1111"),
    "aviso": ("⚠", "Atenção", "#FFF4CE", "#5C3D00"),
    "info": ("ℹ", "Informação", "#E8F0FE", "#0B3D91"),
}

PERMISSOES = {
    "admin": {"cadastrar", "movimentar", "consultar"},
    "estoquista": {"movimentar", "consultar"},
}
ROTULO_PERFIL = {"admin": "Administrador", "estoquista": "Estoquista"}

MSG_GENERICA = (
    "Não foi possível concluir a operação. Tente novamente; se o problema "
    "continuar, procure o administrador do sistema."
)

log = logging.getLogger("livraria")
_manipulador = logging.FileHandler(LOG_PATH, encoding="utf-8", delay=True)
_manipulador.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
log.addHandler(_manipulador)
log.setLevel(logging.ERROR)


# --------------------------------------------------------------------------- #
# Exceções e utilitários de domínio
# --------------------------------------------------------------------------- #
class ErroPermissao(Exception):
    """Usuário sem permissão para a operação."""


class ErroCampo(ValueError):
    """Valor de campo inválido (a mensagem já orienta a correção)."""


class ErroNegocio(Exception):
    """Regra de negócio violada; `campo` indica qual campo destacar (ou None)."""

    def __init__(self, campo, mensagem):
        super().__init__(mensagem)
        self.campo = campo


def plural(n, singular, plural_):
    return f"{n} {singular if n == 1 else plural_}"


def formatar_preco(centavos):
    return f"{centavos // 100},{centavos % 100:02d}"


def normalizar_busca(texto):
    """Minúsculas e sem acentos, para a pesquisa ignorar maiúsculas/acentuação."""
    texto = unicodedata.normalize("NFD", texto.casefold())
    return "".join(c for c in texto if not unicodedata.combining(c))


def normalizar_isbn(texto):
    limpo = re.sub(r"[\s-]", "", texto).upper()
    if re.fullmatch(r"[0-9]{13}", limpo) or re.fullmatch(r"[0-9]{9}[0-9X]", limpo):
        return limpo
    raise ErroCampo(
        "ISBN inválido. Digite 10 ou 13 dígitos (hifens são opcionais). "
        "Exemplo: 978-85-359-0277-5."
    )


def parse_preco(texto):
    limpo = texto.strip().replace("R$", "").replace(" ", "")
    if not re.fullmatch(r"[0-9]{1,6}([.,][0-9]{1,2})?", limpo):
        raise ErroCampo(
            "Digite o preço só com números, usando vírgula ou ponto para os "
            "centavos. Exemplo: 49,90."
        )
    centavos = int((Decimal(limpo.replace(",", ".")) * 100).to_integral_value())
    if centavos <= 0:
        raise ErroCampo("O preço deve ser maior que zero. Exemplo: 49,90.")
    return centavos


def parse_quantidade(texto, minimo):
    texto = texto.strip()
    if not re.fullmatch(r"[0-9]+", texto):
        raise ErroCampo(
            "Informe a quantidade como número inteiro, sem letras, sinais ou "
            "vírgulas. Exemplo: 10."
        )
    n = int(texto)
    if n < minimo:
        raise ErroCampo(f"A quantidade deve ser de pelo menos {minimo}. Exemplo: 10.")
    if n > LIMITE_QTD:
        raise ErroCampo(f"A quantidade máxima por operação é {LIMITE_QTD}. Reduza o valor.")
    return n


def validar_formulario(modo, dados):
    """Retorna (valores_validados, {campo: mensagem_de_erro})."""
    valores, erros = {}, {}

    try:
        valores["isbn"] = normalizar_isbn(dados["isbn"])
    except ErroCampo as e:
        erros["isbn"] = str(e)

    if modo == "cadastro":
        for chave, nome in (("titulo", "título"), ("autor", "autor")):
            texto = " ".join(dados[chave].split())
            if len(texto) < 2:
                erros[chave] = f"Informe o {nome} do livro com pelo menos 2 caracteres."
            elif len(texto) > 150:
                erros[chave] = f"O {nome} passa de 150 caracteres. Abrevie o texto."
            else:
                valores[chave] = texto
        try:
            valores["preco"] = parse_preco(dados["preco"])
        except ErroCampo as e:
            erros["preco"] = str(e)

    try:
        valores["quantidade"] = parse_quantidade(
            dados["quantidade"], minimo=0 if modo == "cadastro" else 1
        )
    except ErroCampo as e:
        erros["quantidade"] = str(e)

    return valores, erros


# --------------------------------------------------------------------------- #
# Sessão e autorização
# --------------------------------------------------------------------------- #
class Sessao:
    def __init__(self, usuario, perfil):
        self.usuario = usuario
        self.perfil = perfil

    def pode(self, permissao):
        return permissao in PERMISSOES.get(self.perfil, set())

    def exigir(self, permissao):
        if not self.pode(permissao):
            raise ErroPermissao("Seu perfil não tem permissão para esta operação.")


# --------------------------------------------------------------------------- #
# Banco de dados
# --------------------------------------------------------------------------- #
SALT_FALSO = b"\x00" * 16  # usado para manter o tempo de resposta igual a usuários inexistentes

LIVROS_DEMO = [  # ISBNs fictícios, apenas para demonstração
    ("9780000000011", "Dom Casmurro", "Machado de Assis", 3990, 12),
    ("9780000000028", "Vidas Secas", "Graciliano Ramos", 3490, 3),
    ("9780000000035", "O Cortiço", "Aluísio Azevedo", 2990, 0),
    ("9780000000042", "A Hora da Estrela", "Clarice Lispector", 3290, 8),
    ("9780000000059", "Grande Sertão: Veredas", "João Guimarães Rosa", 6490, 5),
]


def gerar_hash(senha, salt):
    return hashlib.pbkdf2_hmac("sha256", senha.encode("utf-8"), salt, ITERACOES_HASH)


class Banco:
    def __init__(self, caminho):
        self.con = sqlite3.connect(caminho)
        self.con.row_factory = sqlite3.Row
        self.con.execute("PRAGMA foreign_keys = ON")
        self._criar_tabelas()
        self._dados_iniciais()

    def _criar_tabelas(self):
        with self.con:
            self.con.executescript(
                """
                CREATE TABLE IF NOT EXISTS usuarios (
                    usuario    TEXT PRIMARY KEY,
                    salt       BLOB NOT NULL,
                    senha_hash BLOB NOT NULL,
                    perfil     TEXT NOT NULL CHECK (perfil IN ('admin', 'estoquista'))
                );
                CREATE TABLE IF NOT EXISTS livros (
                    isbn           TEXT PRIMARY KEY,
                    titulo         TEXT NOT NULL,
                    autor          TEXT NOT NULL,
                    preco_centavos INTEGER NOT NULL CHECK (preco_centavos >= 0),
                    quantidade     INTEGER NOT NULL CHECK (quantidade >= 0)
                );
                CREATE TABLE IF NOT EXISTS movimentacoes (
                    id         INTEGER PRIMARY KEY AUTOINCREMENT,
                    isbn       TEXT NOT NULL REFERENCES livros(isbn),
                    tipo       TEXT NOT NULL CHECK (tipo IN ('cadastro', 'entrada', 'saida')),
                    quantidade INTEGER NOT NULL,
                    usuario    TEXT NOT NULL,
                    data_hora  TEXT NOT NULL
                );
                """
            )

    def _dados_iniciais(self):
        if self.con.execute("SELECT COUNT(*) FROM usuarios").fetchone()[0] == 0:
            self.criar_usuario("admin", "admin123", "admin")
            self.criar_usuario("estoque", "estoque123", "estoquista")
            with self.con:
                for isbn, titulo, autor, preco, qtd in LIVROS_DEMO:
                    self.con.execute(
                        "INSERT OR IGNORE INTO livros VALUES (?, ?, ?, ?, ?)",
                        (isbn, titulo, autor, preco, qtd),
                    )

    # -- usuários ----------------------------------------------------------- #
    def criar_usuario(self, usuario, senha, perfil):
        salt = os.urandom(16)
        with self.con:
            self.con.execute(
                "INSERT OR REPLACE INTO usuarios (usuario, salt, senha_hash, perfil) "
                "VALUES (?, ?, ?, ?)",
                (usuario.strip().lower(), salt, gerar_hash(senha, salt), perfil),
            )

    def autenticar(self, usuario, senha):
        linha = self.con.execute(
            "SELECT salt, senha_hash, perfil FROM usuarios WHERE usuario = ?",
            (usuario.strip().lower(),),
        ).fetchone()
        calculado = gerar_hash(senha, linha["salt"] if linha else SALT_FALSO)
        if linha and hmac.compare_digest(calculado, linha["senha_hash"]):
            return linha["perfil"]
        return None

    # -- livros ------------------------------------------------------------- #
    def obter_livro(self, sessao, isbn):
        sessao.exigir("consultar")
        return self.con.execute(
            "SELECT isbn, titulo, autor, preco_centavos, quantidade FROM livros WHERE isbn = ?",
            (isbn,),
        ).fetchone()

    def cadastrar_livro(self, sessao, isbn, titulo, autor, preco_centavos, quantidade):
        sessao.exigir("cadastrar")
        try:
            with self.con:
                self.con.execute(
                    "INSERT INTO livros VALUES (?, ?, ?, ?, ?)",
                    (isbn, titulo, autor, preco_centavos, quantidade),
                )
                self._registrar(isbn, "cadastro", quantidade, sessao.usuario)
        except sqlite3.IntegrityError:
            raise ErroNegocio(
                "isbn",
                "Já existe um livro com este ISBN. Confira o número ou use "
                "“Movimentar estoque” para registrar entradas e saídas.",
            )

    def atualizar_livro(self, sessao, isbn, titulo, autor, preco_centavos):
        sessao.exigir("cadastrar")
        with self.con:
            self.con.execute(
                "UPDATE livros SET titulo = ?, autor = ?, preco_centavos = ? WHERE isbn = ?",
                (titulo, autor, preco_centavos, isbn),
            )

    def movimentar(self, sessao, isbn, tipo, quantidade):
        sessao.exigir("movimentar")
        if tipo not in ("entrada", "saida"):
            raise ValueError("tipo de movimentação inválido")
        with self.con:  # em caso de exceção, tudo é desfeito
            livro = self.con.execute(
                "SELECT titulo, quantidade FROM livros WHERE isbn = ?", (isbn,)
            ).fetchone()
            if livro is None:
                raise ErroNegocio(
                    "isbn",
                    "Nenhum livro com este ISBN. Confira os dígitos ou peça a um "
                    "administrador para cadastrá-lo.",
                )
            if tipo == "saida":
                atual = livro["quantidade"]
                if atual < quantidade:
                    if atual == 0:
                        msg = ("Este livro está esgotado (0 exemplares). Registre uma "
                               "entrada antes de registrar uma saída.")
                    else:
                        msg = (f"Estoque insuficiente: há apenas {plural(atual, 'exemplar', 'exemplares')}. "
                               f"Informe uma quantidade de até {atual}.")
                    raise ErroNegocio("quantidade", msg)
                delta = -quantidade
            else:
                delta = quantidade
            self.con.execute(
                "UPDATE livros SET quantidade = quantidade + ? WHERE isbn = ?", (delta, isbn)
            )
            self._registrar(isbn, tipo, quantidade, sessao.usuario)
            return self.con.execute(
                "SELECT isbn, titulo, quantidade FROM livros WHERE isbn = ?", (isbn,)
            ).fetchone()

    def listar(self, sessao, termo=""):
        """Retorna (linhas_filtradas, total_de_livros, livros_com_estoque_baixo)."""
        sessao.exigir("consultar")
        todos = self.con.execute(
            "SELECT isbn, titulo, autor, quantidade FROM livros ORDER BY titulo COLLATE NOCASE"
        ).fetchall()
        chave = normalizar_busca(termo.strip())
        if chave:
            chave_isbn = re.sub(r"[\s-]", "", chave)
            filtrados = [
                l for l in todos
                if chave in normalizar_busca(f"{l['titulo']} {l['autor']}")
                or (chave_isbn and chave_isbn in l["isbn"].lower())
            ]
        else:
            filtrados = todos
        baixos = sum(1 for l in todos if l["quantidade"] <= ESTOQUE_BAIXO)
        return filtrados, len(todos), baixos

    def _registrar(self, isbn, tipo, quantidade, usuario):
        self.con.execute(
            "INSERT INTO movimentacoes (isbn, tipo, quantidade, usuario, data_hora) "
            "VALUES (?, ?, ?, ?, ?)",
            (isbn, tipo, quantidade, usuario, datetime.now().isoformat(timespec="seconds")),
        )


# --------------------------------------------------------------------------- #
# Componentes de interface acessíveis
# --------------------------------------------------------------------------- #
def fonte(tamanho=12, negrito=False):
    return ("Helvetica", tamanho, "bold") if negrito else ("Helvetica", tamanho)


def garantir_area_minima(widget, minimo=MIN_ALVO):
    """Aumenta o preenchimento interno até o controle ter ao menos 44 × 44 px."""
    widget.update_idletasks()
    falta_x = minimo - widget.winfo_reqwidth()
    falta_y = minimo - widget.winfo_reqheight()
    if falta_x > 0:
        widget.config(padx=int(float(str(widget.cget("padx")))) + math.ceil(falta_x / 2))
    if falta_y > 0:
        widget.config(pady=int(float(str(widget.cget("pady")))) + math.ceil(falta_y / 2))


def criar_botao(pai, texto, comando, primario=True):
    if primario:
        bg, fg, ativo = COR["primaria"], COR["primaria_texto"], COR["primaria_ativa"]
    else:
        bg, fg, ativo = COR["secundaria"], COR["texto"], COR["secundaria_ativa"]
    b = tk.Button(
        pai, text=texto, command=comando, font=fonte(12, True),
        bg=bg, fg=fg, activebackground=ativo, activeforeground=fg,
        disabledforeground=COR["desabilitado_texto"],
        relief="raised", bd=2, padx=20, pady=10, cursor="hand2", takefocus=True,
        highlightthickness=3, highlightbackground=pai.cget("bg"),
        highlightcolor=COR["foco"],
    )
    b._cor_bg, b._cor_fg = bg, fg
    b.bind("<Return>", lambda _e: b.invoke())
    garantir_area_minima(b)
    return b


def definir_habilitado(botao, habilitado):
    if habilitado:
        botao.config(state="normal", bg=botao._cor_bg, fg=botao._cor_fg, cursor="hand2")
    else:
        botao.config(state="disabled", bg=COR["desabilitado_bg"],
                     fg=COR["desabilitado_texto"], cursor="arrow")


class Alerta(tk.Label):
    """Faixa de mensagem com símbolo + texto + cor (nunca só cor)."""

    def __init__(self, pai, largura=720):
        super().__init__(
            pai, text="", justify="left", anchor="w", wraplength=largura,
            padx=14, pady=10, bd=0, highlightthickness=2, font=fonte(12),
        )

    def mostrar(self, tipo, texto):
        simbolo, nome, bg, fg = ALERTAS[tipo]
        self.config(text=f"{simbolo} {nome}: {texto}", bg=bg, fg=fg, highlightbackground=fg)
        self.grid()

    def ocultar(self):
        self.grid_remove()  # o chamador deve ter feito .grid(...) antes


class Campo(tk.Frame):
    """Rótulo persistente + campo de texto + dica + mensagem de erro."""

    def __init__(self, pai, rotulo, dica="", mascarar=False, largura=38, wrap=380):
        bg = pai.cget("bg")
        super().__init__(pai, bg=bg)
        self.bg, self.wrap = bg, wrap
        self.var = tk.StringVar()
        self.rotulo = tk.Label(self, text=rotulo, font=fonte(12, True), bg=bg,
                               fg=COR["texto"], anchor="w")
        self.rotulo.pack(fill="x", pady=(0, 4))
        self.entrada = tk.Entry(
            self, textvariable=self.var, width=largura, font=fonte(13),
            bg=COR["campo"], fg=COR["texto"], insertbackground=COR["texto"],
            disabledbackground=COR["desabilitado_bg"], disabledforeground=COR["texto_suave"],
            relief="solid", bd=1, highlightthickness=3,
            highlightbackground=COR["borda"], highlightcolor=COR["foco"],
            show="•" if mascarar else "",
        )
        self.entrada.pack(fill="x", ipady=10)
        self.dica = tk.Label(self, text="", font=fonte(11), bg=bg, fg=COR["texto_suave"],
                             anchor="w", justify="left", wraplength=wrap)
        self.erro = tk.Label(self, text="", font=fonte(11, True), bg=bg, fg=COR["erro_fg"],
                             anchor="w", justify="left", wraplength=wrap)
        self.definir_dica(dica)

    def valor(self):
        return self.var.get()

    def definir(self, texto):
        self.var.set(texto)

    def habilitar(self, sim):
        self.entrada.config(state="normal" if sim else "disabled")

    def mostrar_senha(self, sim):
        self.entrada.config(show="" if sim else "•")

    def definir_rotulo(self, rotulo, dica=""):
        self.rotulo.config(text=rotulo)
        self.definir_dica(dica)

    def definir_dica(self, texto):
        self.dica.config(text=texto)
        if texto:
            opcoes = {"fill": "x", "pady": (4, 0)}
            if self.erro.winfo_manager():
                opcoes["before"] = self.erro
            self.dica.pack(**opcoes)
        else:
            self.dica.pack_forget()

    def tem_erro(self):
        return bool(self.erro.winfo_manager())

    def mostrar_erro(self, texto):
        self.erro.config(text=f"✖ {texto}")
        self.erro.pack(fill="x", pady=(4, 0))
        self.entrada.config(highlightbackground=COR["erro_fg"])

    def limpar_erro(self):
        self.erro.pack_forget()
        self.entrada.config(highlightbackground=COR["borda"])


class Seletor(tk.Frame):
    """Grupo de botões de opção (Entrada/Saída) com marcador ●/○ além da cor."""

    def __init__(self, pai, rotulo, opcoes, comando=None):
        bg = pai.cget("bg")
        super().__init__(pai, bg=bg)
        self.var = tk.StringVar(value=opcoes[0][0])
        self.opcoes = dict(opcoes)
        self.comando = comando
        tk.Label(self, text=rotulo, font=fonte(12, True), bg=bg, fg=COR["texto"],
                 anchor="w").pack(fill="x", pady=(0, 4))
        linha = tk.Frame(self, bg=bg)
        linha.pack(anchor="w")
        self.botoes = {}
        for valor, texto in opcoes:
            rb = tk.Radiobutton(
                linha, text=texto, value=valor, variable=self.var, command=self._mudou,
                indicatoron=False, font=fonte(12, True), bg=COR["secundaria"],
                fg=COR["texto"], selectcolor=COR["selecao"],
                activebackground=COR["secundaria_ativa"], activeforeground=COR["texto"],
                relief="raised", bd=2, padx=24, pady=10, cursor="hand2", takefocus=True,
                highlightthickness=3, highlightbackground=bg, highlightcolor=COR["foco"],
            )
            rb.pack(side="left", padx=(0, 8))
            rb.bind("<Return>", lambda _e, r=rb: r.invoke())
            self.botoes[valor] = rb
        self._atualizar()
        for rb in self.botoes.values():
            garantir_area_minima(rb)

    def _atualizar(self):
        for valor, rb in self.botoes.items():
            marca = "● " if self.var.get() == valor else "○ "
            rb.config(text=marca + self.opcoes[valor])

    def _mudou(self):
        self._atualizar()
        if self.comando:
            self.comando()

    def definir(self, valor):
        self.var.set(valor)
        self._atualizar()


def configurar_estilos(raiz):
    estilo = ttk.Style(raiz)
    estilo.theme_use("clam")
    estilo.configure("Treeview", background=COR["campo"], fieldbackground=COR["campo"],
                     foreground=COR["texto"], font=fonte(12), rowheight=38,
                     bordercolor=COR["borda"], borderwidth=1)
    estilo.configure("Treeview.Heading", background=COR["primaria"],
                     foreground=COR["primaria_texto"], font=fonte(12, True),
                     padding=(8, 10), relief="flat")
    estilo.map("Treeview.Heading", background=[("active", COR["primaria_ativa"])])
    estilo.map("Treeview", background=[("selected", COR["primaria"])],
               foreground=[("selected", COR["primaria_texto"])])
    estilo.configure("Vertical.TScrollbar", arrowsize=30, background=COR["secundaria"],
                     troughcolor=COR["fundo_alt"])


# --------------------------------------------------------------------------- #
# TELA 1 — Menu inicial com autenticação
# --------------------------------------------------------------------------- #
class TelaMenu(tk.Frame):
    FUNCOES = (
        ("cadastro", "Cadastrar livro", "cadastrar"),
        ("movimentacao", "Movimentar estoque", "movimentar"),
        ("consulta", "Consultar estoque", "consultar"),
    )

    def __init__(self, pai, app):
        super().__init__(pai, bg=COR["fundo"])
        self.app = app
        self.tentativas = 0
        self.bloqueado_ate = 0.0
        self.columnconfigure(0, weight=1)

        corpo = tk.Frame(self, bg=COR["fundo"])
        corpo.grid(row=0, column=0, pady=24)
        tk.Label(corpo, text="Livraria — Controle de Estoque", font=fonte(24, True),
                 bg=COR["fundo"], fg=COR["texto"]).grid(row=0, column=0, sticky="w")
        tk.Label(corpo, text="Entre com seu usuário e senha para acessar as funções do sistema.",
                 font=fonte(12), bg=COR["fundo"], fg=COR["texto_suave"]).grid(
            row=1, column=0, sticky="w", pady=(4, 0))

        # --- cartão de login ---
        login = tk.Frame(corpo, bg=COR["fundo_alt"], padx=24, pady=20,
                         highlightthickness=1, highlightbackground=COR["borda"])
        login.grid(row=2, column=0, sticky="ew", pady=(16, 16))
        login.columnconfigure(0, weight=1)

        self.campo_usuario = Campo(login, "Usuário", largura=40, wrap=440)
        self.campo_usuario.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        self.campo_senha = Campo(login, "Senha", mascarar=True, largura=40, wrap=440)
        self.campo_senha.grid(row=1, column=0, sticky="ew")

        self.var_mostrar = tk.BooleanVar(value=False)
        chk = tk.Checkbutton(
            login, text="Mostrar senha", variable=self.var_mostrar, command=self._alternar_senha,
            font=fonte(12), bg=COR["fundo_alt"], fg=COR["texto"],
            activebackground=COR["fundo_alt"], activeforeground=COR["texto"],
            selectcolor=COR["campo"], anchor="w", padx=6, pady=10, takefocus=True,
            highlightthickness=3, highlightbackground=COR["fundo_alt"],
            highlightcolor=COR["foco"],
        )
        chk.grid(row=2, column=0, sticky="w")
        garantir_area_minima(chk)

        self.alerta = Alerta(login, 440)
        self.alerta.grid(row=3, column=0, sticky="ew", pady=(0, 10))
        self.alerta.ocultar()

        linha = tk.Frame(login, bg=COR["fundo_alt"])
        linha.grid(row=4, column=0, sticky="ew")
        self.btn_entrar = criar_botao(linha, "Entrar", self._entrar)
        self.btn_entrar.pack(side="left", fill="x", expand=True, padx=(0, 8))
        self.btn_sair = criar_botao(linha, "Sair", self._sair, primario=False)
        self.btn_sair.pack(side="left", fill="x", expand=True)

        for campo in (self.campo_usuario, self.campo_senha):
            campo.entrada.bind("<Return>", lambda _e: self._entrar())

        # --- funções do sistema ---
        funcoes = tk.Frame(corpo, bg=COR["fundo"])
        funcoes.grid(row=3, column=0, sticky="ew")
        funcoes.columnconfigure(0, weight=1)
        tk.Label(funcoes, text="Funções do sistema", font=fonte(16, True),
                 bg=COR["fundo"], fg=COR["texto"]).grid(row=0, column=0, sticky="w", pady=(0, 8))
        self.botoes = {}
        for i, (chave, texto, _perm) in enumerate(self.FUNCOES):
            b = criar_botao(funcoes, texto, lambda c=chave: self._abrir(c))
            b.grid(row=i + 1, column=0, sticky="ew", pady=4)
            self.botoes[chave] = b
        self.dica_funcoes = tk.Label(funcoes, text="", font=fonte(11), bg=COR["fundo"],
                                     fg=COR["texto_suave"], anchor="w", justify="left",
                                     wraplength=440)
        self.dica_funcoes.grid(row=len(self.FUNCOES) + 1, column=0, sticky="w", pady=(6, 0))

    # -- ciclo de vida -------------------------------------------------------
    def ao_exibir(self, **_):
        self._atualizar_estado()
        sessao = self.app.sessao
        if sessao is None:
            self.campo_usuario.entrada.focus_set()
        else:
            for chave, _t, perm in self.FUNCOES:
                if sessao.pode(perm):
                    self.botoes[chave].focus_set()
                    break

    def _atualizar_estado(self):
        sessao = self.app.sessao
        logado = sessao is not None
        self.campo_usuario.habilitar(not logado)
        self.campo_senha.habilitar(not logado)
        definir_habilitado(self.btn_entrar, not logado)
        definir_habilitado(self.btn_sair, logado)
        for chave, _t, perm in self.FUNCOES:
            definir_habilitado(self.botoes[chave], logado and sessao.pode(perm))
        if logado:
            self.alerta.mostrar(
                "ok", f"Sessão iniciada como {sessao.usuario} ({ROTULO_PERFIL[sessao.perfil]}).")
            if not sessao.pode("cadastrar"):
                self.dica_funcoes.config(
                    text="“Cadastrar livro” está disponível apenas para administradores.")
            else:
                self.dica_funcoes.config(text="")
        else:
            self.alerta.ocultar()
            self.dica_funcoes.config(text="Entre no sistema para habilitar as funções.")

    # -- ações ---------------------------------------------------------------
    def _alternar_senha(self):
        self.campo_senha.mostrar_senha(self.var_mostrar.get())

    def _entrar(self):
        if self.app.sessao is not None:
            return
        self.campo_usuario.limpar_erro()
        self.campo_senha.limpar_erro()

        restante = self.bloqueado_ate - time.monotonic()
        if restante > 0:
            self.alerta.mostrar(
                "erro", f"Muitas tentativas incorretas. Aguarde {math.ceil(restante)} "
                        "segundos e tente novamente.")
            return

        usuario, senha = self.campo_usuario.valor().strip(), self.campo_senha.valor()
        faltando = False
        if not usuario:
            self.campo_usuario.mostrar_erro("Informe o usuário.")
            self.campo_usuario.entrada.focus_set()
            faltando = True
        if not senha:
            self.campo_senha.mostrar_erro("Informe a senha.")
            if not faltando:
                self.campo_senha.entrada.focus_set()
            faltando = True
        if faltando:
            self.alerta.mostrar("erro", "Preencha usuário e senha para entrar.")
            return

        try:
            perfil = self.app.banco.autenticar(usuario, senha)
        except Exception:
            log.exception("Falha na autenticação")
            self.alerta.mostrar("erro", MSG_GENERICA)
            return

        if perfil is None:
            self.tentativas += 1
            self.campo_senha.definir("")
            if self.tentativas >= MAX_TENTATIVAS:
                self.tentativas = 0
                self.bloqueado_ate = time.monotonic() + BLOQUEIO_SEGUNDOS
                self.alerta.mostrar(
                    "erro", f"Muitas tentativas incorretas. Aguarde {BLOQUEIO_SEGUNDOS} "
                            "segundos e tente novamente.")
            else:
                restam = MAX_TENTATIVAS - self.tentativas
                self.alerta.mostrar(
                    "erro", "Usuário ou senha incorretos. Confira os dados e tente novamente "
                            f"({plural(restam, 'tentativa restante', 'tentativas restantes')}).")
            self.campo_senha.entrada.focus_set()
            return

        self.tentativas = 0
        self.app.sessao = Sessao(usuario.lower(), perfil)
        self.campo_senha.definir("")
        self.ao_exibir()

    def _sair(self):
        self.app.sessao = None
        self.campo_usuario.definir("")
        self.campo_senha.definir("")
        self.ao_exibir()

    def _abrir(self, chave):
        sessao = self.app.sessao
        permissao = {c: p for c, _t, p in self.FUNCOES}[chave]
        if sessao is None or not sessao.pode(permissao):
            return
        if chave == "consulta":
            self.app.mostrar("TelaResultados")
        else:
            self.app.mostrar("TelaOperacao", modo=chave)


# --------------------------------------------------------------------------- #
# TELA 2 — Cadastro e movimentação
# --------------------------------------------------------------------------- #
class TelaOperacao(tk.Frame):
    ORDEM = ("titulo", "autor", "isbn", "preco", "quantidade")

    def __init__(self, pai, app):
        super().__init__(pai, bg=COR["fundo"])
        self.app = app
        self.modo = "cadastro"
        self.estoque_atual = None
        self._dica_base = ""
        self.columnconfigure(0, weight=1)

        corpo = tk.Frame(self, bg=COR["fundo"])
        corpo.grid(row=0, column=0, padx=40, pady=24, sticky="n")
        corpo.columnconfigure(0, weight=1, uniform="col")
        corpo.columnconfigure(1, weight=1, uniform="col")

        self.titulo = tk.Label(corpo, font=fonte(22, True), bg=COR["fundo"], fg=COR["texto"],
                               anchor="w")
        self.titulo.grid(row=0, column=0, columnspan=2, sticky="w")
        self.subtitulo = tk.Label(corpo, font=fonte(12), bg=COR["fundo"],
                                  fg=COR["texto_suave"], anchor="w", justify="left",
                                  wraplength=820)
        self.subtitulo.grid(row=1, column=0, columnspan=2, sticky="w", pady=(4, 0))

        self.alerta = Alerta(corpo, 820)
        self.alerta.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(12, 0))
        self.alerta.ocultar()

        self.seletor = Seletor(corpo, "Operação",
                               [("entrada", "Entrada"), ("saida", "Saída")],
                               comando=self._mudou_operacao)
        self.seletor.grid(row=3, column=0, columnspan=2, sticky="w", pady=(14, 0))

        self.campos = {
            "titulo": Campo(corpo, "Título"),
            "autor": Campo(corpo, "Autor"),
            "isbn": Campo(corpo, "ISBN", dica="10 ou 13 dígitos; os hifens são opcionais."),
            "preco": Campo(corpo, "Preço (R$)", dica="Use vírgula ou ponto nos centavos. Exemplo: 49,90."),
            "quantidade": Campo(corpo, "Quantidade"),
        }
        posicoes = {"titulo": (4, 0), "autor": (4, 1), "isbn": (5, 0),
                    "preco": (5, 1), "quantidade": (6, 0)}
        for chave, (linha, coluna) in posicoes.items():
            self.campos[chave].grid(row=linha, column=coluna, sticky="new",
                                    padx=(0, 20) if coluna == 0 else 0, pady=(14, 0))
            self.campos[chave].entrada.bind("<Return>", lambda _e, k=chave: self._ao_enter(k))
        self.campos["isbn"].entrada.bind("<FocusOut>", self._buscar_isbn)

        botoes = tk.Frame(corpo, bg=COR["fundo"])
        botoes.grid(row=7, column=0, columnspan=2, sticky="w", pady=(24, 0))
        self.btn_salvar = criar_botao(botoes, "Salvar cadastro", self._enviar)
        self.btn_salvar.pack(side="left", padx=(0, 10))
        self.btn_voltar = criar_botao(botoes, "Voltar", self.voltar, primario=False)
        self.btn_voltar.pack(side="left")

    # -- ciclo de vida -------------------------------------------------------
    def ao_exibir(self, modo="cadastro"):
        self.modo = modo
        self.estoque_atual = None
        self.alerta.ocultar()
        for campo in self.campos.values():
            campo.limpar_erro()
            campo.habilitar(True)
            campo.definir("")
        q = self.campos["quantidade"]
        if modo == "cadastro":
            self.titulo.config(text="Cadastrar livro")
            self.subtitulo.config(text="Preencha os dados do novo livro. Se o ISBN já existir, "
                                       "você poderá atualizar título, autor e preço.")
            self.seletor.grid_remove()
            q.definir_rotulo("Quantidade em estoque",
                             "Exemplares disponíveis agora. Use 0 se ainda não houver.")
            self.btn_salvar.config(text="Salvar cadastro")
            primeiro = "titulo"
        else:
            self.titulo.config(text="Movimentar estoque")
            self.subtitulo.config(text="Informe o ISBN e a quantidade. Título, autor e preço "
                                       "são preenchidos automaticamente.")
            self.seletor.grid()
            self.seletor.definir("entrada")
            for chave in ("titulo", "autor", "preco"):
                self.campos[chave].habilitar(False)
            q.definir_rotulo("Quantidade")
            self._mudou_operacao()
            self.btn_salvar.config(text="Registrar movimentação")
            primeiro = "isbn"
        garantir_area_minima(self.btn_salvar)
        self.campos[primeiro].entrada.focus_set()

    def voltar(self):
        self.app.mostrar("TelaMenu")

    # -- movimentação: dica de quantidade e busca por ISBN ---------------------
    def _mudou_operacao(self):
        saida = self.seletor.var.get() == "saida"
        self._dica_base = ("Exemplares que saíram do estoque (venda, perda ou devolução)."
                           if saida else "Exemplares que chegaram ao estoque.")
        self._atualizar_dica()

    def _atualizar_dica(self):
        texto = self._dica_base
        if self.estoque_atual is not None:
            texto += f" Em estoque agora: {self.estoque_atual}."
        self.campos["quantidade"].definir_dica(texto)

    def _limpar_livro(self):
        for chave in ("titulo", "autor", "preco"):
            self.campos[chave].definir("")
        self.estoque_atual = None
        self._atualizar_dica()

    def _buscar_isbn(self, _evento=None):
        if self.modo != "movimentacao":
            return
        campo = self.campos["isbn"]
        bruto = campo.valor().strip()
        if not bruto:
            return
        try:
            isbn = normalizar_isbn(bruto)
        except ErroCampo as e:
            campo.mostrar_erro(str(e))
            self._limpar_livro()
            return
        try:
            livro = self.app.banco.obter_livro(self.app.sessao, isbn)
        except Exception:
            log.exception("Falha ao buscar ISBN")
            self.alerta.mostrar("erro", MSG_GENERICA)
            return
        if livro is None:
            campo.mostrar_erro("Nenhum livro com este ISBN. Confira os dígitos ou peça a um "
                               "administrador para cadastrá-lo.")
            self._limpar_livro()
            return
        campo.limpar_erro()
        self.campos["titulo"].definir(livro["titulo"])
        self.campos["autor"].definir(livro["autor"])
        self.campos["preco"].definir(formatar_preco(livro["preco_centavos"]))
        self.estoque_atual = livro["quantidade"]
        self._atualizar_dica()

    def _ao_enter(self, chave):
        if self.modo == "movimentacao" and chave == "isbn":
            self._buscar_isbn()
            if not self.campos["isbn"].tem_erro():
                self.campos["quantidade"].entrada.focus_set()
            return
        self._enviar()

    # -- envio ---------------------------------------------------------------
    def _mostrar_erros(self, erros):
        primeiro = None
        for chave in self.ORDEM:
            if chave in erros:
                self.campos[chave].mostrar_erro(erros[chave])
                primeiro = primeiro or chave
        n = len(erros)
        self.alerta.mostrar(
            "erro", "Corrija o campo indicado abaixo e tente novamente." if n == 1
            else f"Corrija os {n} campos indicados abaixo e tente novamente.")
        if primeiro:
            self.campos[primeiro].entrada.focus_set()

    def _enviar(self):
        for campo in self.campos.values():
            campo.limpar_erro()
        self.alerta.ocultar()
        dados = {chave: campo.valor() for chave, campo in self.campos.items()}
        valores, erros = validar_formulario(self.modo, dados)
        if erros:
            self._mostrar_erros(erros)
            return
        try:
            if self.modo == "cadastro":
                self._salvar_cadastro(valores)
            else:
                self._registrar_movimentacao(valores)
        except ErroNegocio as e:
            if e.campo in self.campos:
                self._mostrar_erros({e.campo: str(e)})
            else:
                self.alerta.mostrar("erro", str(e))
        except ErroPermissao as e:
            self.alerta.mostrar("erro", str(e))
        except Exception:
            log.exception("Falha ao salvar operação")
            self.alerta.mostrar("erro", MSG_GENERICA)

    def _salvar_cadastro(self, v):
        banco, sessao = self.app.banco, self.app.sessao
        existente = banco.obter_livro(sessao, v["isbn"])
        if existente:
            sessao.exigir("cadastrar")
            atualizar = messagebox.askyesno(
                "ISBN já cadastrado",
                f"O ISBN {v['isbn']} já está cadastrado como “{existente['titulo']}”.\n\n"
                "Deseja atualizar título, autor e preço com os dados informados?\n"
                "A quantidade em estoque não será alterada; para isso use "
                "“Movimentar estoque”.",
                parent=self.app)
            if not atualizar:
                self.campos["isbn"].entrada.focus_set()
                return
            banco.atualizar_livro(sessao, v["isbn"], v["titulo"], v["autor"], v["preco"])
            mensagem = (f"Dados de “{v['titulo']}” atualizados. Estoque mantido em "
                        f"{plural(existente['quantidade'], 'exemplar', 'exemplares')}.")
        else:
            banco.cadastrar_livro(sessao, v["isbn"], v["titulo"], v["autor"],
                                  v["preco"], v["quantidade"])
            mensagem = (f"Livro “{v['titulo']}” cadastrado com "
                        f"{plural(v['quantidade'], 'exemplar', 'exemplares')} em estoque.")
        self.app.mostrar("TelaResultados", mensagem=mensagem, tipo="ok", destaque=v["isbn"])

    def _registrar_movimentacao(self, v):
        tipo = self.seletor.var.get()
        livro = self.app.banco.movimentar(self.app.sessao, v["isbn"], tipo, v["quantidade"])
        rotulo, sinal = ("Entrada", "+") if tipo == "entrada" else ("Saída", "−")
        mensagem = (f"{rotulo} registrada: {sinal}{plural(v['quantidade'], 'exemplar', 'exemplares')} "
                    f"de “{livro['titulo']}”. Estoque atual: {livro['quantidade']}.")
        self.app.mostrar("TelaResultados", mensagem=mensagem, tipo="ok", destaque=v["isbn"])


# --------------------------------------------------------------------------- #
# TELA 3 — Alertas, listagem e resultados
# --------------------------------------------------------------------------- #
class TelaResultados(tk.Frame):
    def __init__(self, pai, app):
        super().__init__(pai, bg=COR["fundo"])
        self.app = app
        self._ultimo_termo = None
        self.rowconfigure(0, weight=1)
        self.columnconfigure(0, weight=1)

        corpo = tk.Frame(self, bg=COR["fundo"])
        corpo.grid(row=0, column=0, sticky="nsew", padx=40, pady=24)
        corpo.columnconfigure(0, weight=1)
        corpo.rowconfigure(5, weight=1)

        tk.Label(corpo, text="Resultado e estoque atual", font=fonte(22, True),
                 bg=COR["fundo"], fg=COR["texto"]).grid(row=0, column=0, sticky="w")

        self.alerta_operacao = Alerta(corpo, 860)
        self.alerta_operacao.grid(row=1, column=0, sticky="ew", pady=(10, 0))
        self.alerta_operacao.ocultar()
        self.alerta_estoque = Alerta(corpo, 860)
        self.alerta_estoque.grid(row=2, column=0, sticky="ew", pady=(8, 0))
        self.alerta_estoque.ocultar()

        busca = tk.Frame(corpo, bg=COR["fundo"])
        busca.grid(row=3, column=0, sticky="ew", pady=(14, 6))
        busca.columnconfigure(0, weight=1)
        self.campo_busca = Campo(busca, "Pesquisar livro (título, autor ou ISBN)",
                                 largura=40, wrap=500)
        self.campo_busca.grid(row=0, column=0, sticky="ew")
        criar_botao(busca, "Pesquisar", self._pesquisar).grid(
            row=0, column=1, sticky="s", padx=(10, 0))
        criar_botao(busca, "Limpar", self._limpar, primario=False).grid(
            row=0, column=2, sticky="s", padx=(8, 0))
        self.campo_busca.entrada.bind("<Return>", lambda _e: self._pesquisar())
        self.campo_busca.entrada.bind("<KeyRelease>", lambda _e: self._pesquisar(se_mudou=True))

        self.contagem = tk.Label(corpo, text="", font=fonte(11), bg=COR["fundo"],
                                 fg=COR["texto_suave"], anchor="w")
        self.contagem.grid(row=4, column=0, sticky="w", pady=(0, 6))

        # moldura que desenha o anel de foco em volta da tabela
        self.moldura = tk.Frame(corpo, bg=COR["fundo"], highlightthickness=3,
                                highlightbackground=COR["fundo"], highlightcolor=COR["foco"])
        self.moldura.grid(row=5, column=0, sticky="nsew")
        self.moldura.rowconfigure(0, weight=1)
        self.moldura.columnconfigure(0, weight=1)

        self.tabela = ttk.Treeview(
            self.moldura, columns=("titulo", "autor", "quantidade", "situacao"),
            show="headings", selectmode="browse")
        for coluna, texto, largura, ancora, estica in (
                ("titulo", "Título", 320, "w", True), ("autor", "Autor", 220, "w", True),
                ("quantidade", "Quantidade disponível", 190, "e", False),
                ("situacao", "Situação", 160, "w", False)):
            self.tabela.heading(coluna, text=texto, anchor=ancora)
            self.tabela.column(coluna, width=largura, anchor=ancora, stretch=estica)
        self.tabela.tag_configure("baixo", background="#FFF4CE", foreground="#5C3D00")
        self.tabela.tag_configure("zerado", background="#FDECEA", foreground="#8A1111")
        barra = ttk.Scrollbar(self.moldura, orient="vertical", command=self.tabela.yview)
        self.tabela.configure(yscrollcommand=barra.set)
        self.tabela.grid(row=0, column=0, sticky="nsew")
        barra.grid(row=0, column=1, sticky="ns")
        self.tabela.bind("<FocusIn>", lambda _e: self.moldura.config(highlightbackground=COR["foco"]))
        self.tabela.bind("<FocusOut>", lambda _e: self.moldura.config(highlightbackground=COR["fundo"]))

        botoes = tk.Frame(corpo, bg=COR["fundo"])
        botoes.grid(row=6, column=0, sticky="w", pady=(14, 0))
        criar_botao(botoes, "Voltar ao menu", self.voltar).pack(side="left")

    # -- ciclo de vida -------------------------------------------------------
    def ao_exibir(self, mensagem=None, tipo="ok", destaque=None):
        self.campo_busca.definir("")
        self._ultimo_termo = None
        if mensagem:
            self.alerta_operacao.mostrar(tipo, mensagem)
        else:
            self.alerta_operacao.ocultar()
        self._atualizar_tabela(destaque)
        self.campo_busca.entrada.focus_set()

    def voltar(self):
        self.app.mostrar("TelaMenu")

    # -- pesquisa ------------------------------------------------------------
    def _pesquisar(self, se_mudou=False):
        termo = self.campo_busca.valor().strip()
        if se_mudou and termo == self._ultimo_termo:
            return
        self._atualizar_tabela()

    def _limpar(self):
        self.campo_busca.definir("")
        self._atualizar_tabela()
        self.campo_busca.entrada.focus_set()

    def _atualizar_tabela(self, destaque=None):
        termo = self.campo_busca.valor().strip()
        self._ultimo_termo = termo
        try:
            linhas, total, baixos = self.app.banco.listar(self.app.sessao, termo)
        except ErroPermissao as e:
            self.alerta_operacao.mostrar("erro", str(e))
            return
        except Exception:
            log.exception("Falha ao listar estoque")
            self.alerta_operacao.mostrar("erro", MSG_GENERICA)
            return

        self.tabela.delete(*self.tabela.get_children())
        for l in linhas:
            q = l["quantidade"]
            if q == 0:
                situacao, tag = "✖ Esgotado", "zerado"
            elif q <= ESTOQUE_BAIXO:
                situacao, tag = "⚠ Estoque baixo", "baixo"
            else:
                situacao, tag = "✔ Disponível", "ok"
            self.tabela.insert("", "end", iid=l["isbn"],
                               values=(l["titulo"], l["autor"], q, situacao), tags=(tag,))
        if destaque and self.tabela.exists(destaque):
            self.tabela.selection_set(destaque)
            self.tabela.see(destaque)

        self.contagem.config(text=f"Exibindo {len(linhas)} de {total} livro(s).")
        if termo and not linhas:
            self.alerta_estoque.mostrar(
                "aviso", f"Nenhum livro encontrado para “{termo}”. Confira a grafia ou "
                         "pesquise por apenas parte do título, autor ou ISBN.")
        elif baixos:
            verbo = "livro está" if baixos == 1 else "livros estão"
            self.alerta_estoque.mostrar(
                "aviso", f"{baixos} {verbo} com estoque baixo ou esgotado (até "
                         f"{ESTOQUE_BAIXO} exemplares). Considere registrar uma entrada.")
        else:
            self.alerta_estoque.ocultar()


# --------------------------------------------------------------------------- #
# Aplicação
# --------------------------------------------------------------------------- #
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Livraria — Controle de Estoque")
        self.geometry("1000x760")
        self.minsize(900, 700)
        self.configure(bg=COR["fundo"])
        configurar_estilos(self)

        self.banco = Banco(DB_PATH)
        self.sessao = None
        self.atual = None

        container = tk.Frame(self, bg=COR["fundo"])
        container.pack(fill="both", expand=True)
        container.rowconfigure(0, weight=1)
        container.columnconfigure(0, weight=1)

        self.telas = {}
        for Classe in (TelaMenu, TelaOperacao, TelaResultados):
            tela = Classe(container, self)
            tela.grid(row=0, column=0, sticky="nsew")
            self.telas[Classe.__name__] = tela

        self.bind("<Escape>", self._escape)
        self.mostrar("TelaMenu")

    def mostrar(self, nome, **kwargs):
        # grid_remove tira as outras telas da ordem de Tab (tkraise não tiraria)
        for tela in self.telas.values():
            tela.grid_remove()
        self.atual = self.telas[nome]
        self.atual.grid()
        self.atual.ao_exibir(**kwargs)

    def _escape(self, _evento):
        voltar = getattr(self.atual, "voltar", None)
        if voltar:
            voltar()


def ativar_dpi_windows():
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass


def criar_usuario_cli(usuario, perfil):
    if perfil not in PERMISSOES:
        sys.exit(f"Perfil inválido. Use: {', '.join(PERMISSOES)}.")
    senha = getpass.getpass("Senha (mínimo 8 caracteres): ")
    if len(senha) < 8:
        sys.exit("Senha curta demais. Use pelo menos 8 caracteres.")
    if senha != getpass.getpass("Repita a senha: "):
        sys.exit("As senhas não conferem.")
    Banco(DB_PATH).criar_usuario(usuario, senha, perfil)
    print(f"Usuário '{usuario.strip().lower()}' salvo com o perfil '{perfil}'.")


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "--criar-usuario":
        criar_usuario_cli(sys.argv[2], sys.argv[3])
        return
    ativar_dpi_windows()
    App().mainloop()


if __name__ == "__main__":
    main()
