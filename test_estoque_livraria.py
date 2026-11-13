# -*- coding: utf-8 -*-
"""
Testes automatizados do Controle de Estoque da Livraria.

- Testes UNITÁRIOS: funções puras (validação, formatação, permissões), sem banco.
- Testes de INTEGRAÇÃO: a camada Banco conversando com um SQLite real (arquivo
  temporário, criado do zero em cada teste, então um teste nunca afeta o outro).

Executar (na mesma pasta de estoque_livraria.py):
    python -m unittest -v
Cobertura:
    pip install coverage
    coverage run -m unittest
    coverage report -m
    coverage html          # abre htmlcov/index.html com o relatório visual
"""

import shutil
import sqlite3
import tempfile
import unittest
from pathlib import Path

import estoque_livraria as app


# --------------------------------------------------------------------------- #
# TESTES UNITÁRIOS
# --------------------------------------------------------------------------- #
class TestIsbn(unittest.TestCase):
    def test_aceita_isbn13_com_hifens(self):
        self.assertEqual(app.normalizar_isbn("978-85-359-0277-5"), "9788535902775")

    def test_aceita_isbn10_com_x_final(self):
        self.assertEqual(app.normalizar_isbn("85-359-0277-x"), "853590277X")

    def test_rejeita_tamanho_invalido(self):
        with self.assertRaises(app.ErroCampo):
            app.normalizar_isbn("12345")

    def test_rejeita_letras(self):
        with self.assertRaises(app.ErroCampo):
            app.normalizar_isbn("97885359ABCDE")


class TestPreco(unittest.TestCase):
    def test_virgula_e_ponto(self):
        self.assertEqual(app.parse_preco("49,90"), 4990)
        self.assertEqual(app.parse_preco("49.9"), 4990)

    def test_aceita_prefixo_rs(self):
        self.assertEqual(app.parse_preco("R$ 10"), 1000)

    def test_rejeita_zero_texto_e_negativo(self):
        for ruim in ("0", "0,00", "abc", "-5", "1,234", ""):
            with self.subTest(valor=ruim):
                with self.assertRaises(app.ErroCampo):
                    app.parse_preco(ruim)

    def test_formatar_preco(self):
        self.assertEqual(app.formatar_preco(4990), "49,90")
        self.assertEqual(app.formatar_preco(5), "0,05")


class TestQuantidade(unittest.TestCase):
    def test_valores_validos(self):
        self.assertEqual(app.parse_quantidade("10", minimo=1), 10)
        self.assertEqual(app.parse_quantidade("0", minimo=0), 0)

    def test_abaixo_do_minimo(self):
        with self.assertRaises(app.ErroCampo):
            app.parse_quantidade("0", minimo=1)

    def test_acima_do_limite(self):
        with self.assertRaises(app.ErroCampo):
            app.parse_quantidade(str(app.LIMITE_QTD + 1), minimo=1)

    def test_nao_numerico(self):
        for ruim in ("", "dez", "1,5", "-3", "2.0"):
            with self.subTest(valor=ruim):
                with self.assertRaises(app.ErroCampo):
                    app.parse_quantidade(ruim, minimo=0)


class TestValidarFormulario(unittest.TestCase):
    def dados(self, **extra):
        base = {"titulo": "Dom Casmurro", "autor": "Machado de Assis",
                "isbn": "978-85-359-0277-5", "preco": "39,90", "quantidade": "5"}
        base.update(extra)
        return base

    def test_cadastro_valido_normaliza_os_dados(self):
        valores, erros = app.validar_formulario("cadastro", self.dados(titulo="  Dom   Casmurro "))
        self.assertEqual(erros, {})
        self.assertEqual(valores["titulo"], "Dom Casmurro")
        self.assertEqual(valores["preco"], 3990)
        self.assertEqual(valores["isbn"], "9788535902775")

    def test_cadastro_reporta_todos_os_erros_de_uma_vez(self):
        _, erros = app.validar_formulario(
            "cadastro", self.dados(titulo="", autor="", isbn="1", preco="x", quantidade="-1"))
        self.assertEqual(set(erros), {"titulo", "autor", "isbn", "preco", "quantidade"})

    def test_cadastro_aceita_quantidade_zero(self):
        _, erros = app.validar_formulario("cadastro", self.dados(quantidade="0"))
        self.assertEqual(erros, {})

    def test_movimentacao_valida_so_isbn_e_quantidade(self):
        valores, erros = app.validar_formulario(
            "movimentacao", {"isbn": "9780000000011", "quantidade": "3",
                             "titulo": "", "autor": "", "preco": ""})
        self.assertEqual(erros, {})
        self.assertEqual(valores, {"isbn": "9780000000011", "quantidade": 3})

    def test_movimentacao_exige_quantidade_minima_1(self):
        _, erros = app.validar_formulario(
            "movimentacao", {"isbn": "9780000000011", "quantidade": "0",
                             "titulo": "", "autor": "", "preco": ""})
        self.assertIn("quantidade", erros)

    def test_titulo_longo_demais(self):
        _, erros = app.validar_formulario("cadastro", self.dados(titulo="A" * 151))
        self.assertIn("titulo", erros)


class TestUtilitarios(unittest.TestCase):
    def test_busca_ignora_acentos_e_caixa(self):
        self.assertEqual(app.normalizar_busca("Aluísio AZEVEDO"), "aluisio azevedo")

    def test_plural(self):
        self.assertEqual(app.plural(1, "exemplar", "exemplares"), "1 exemplar")
        self.assertEqual(app.plural(2, "exemplar", "exemplares"), "2 exemplares")


class TestSessaoPermissoes(unittest.TestCase):
    def test_admin_pode_tudo(self):
        s = app.Sessao("ana", "admin")
        for p in ("cadastrar", "movimentar", "consultar"):
            self.assertTrue(s.pode(p))

    def test_estoquista_nao_cadastra(self):
        s = app.Sessao("beto", "estoquista")
        self.assertTrue(s.pode("movimentar"))
        self.assertFalse(s.pode("cadastrar"))
        with self.assertRaises(app.ErroPermissao):
            s.exigir("cadastrar")

    def test_perfil_desconhecido_nao_pode_nada(self):
        self.assertFalse(app.Sessao("x", "intruso").pode("consultar"))


# --------------------------------------------------------------------------- #
# TESTES DE INTEGRAÇÃO (Banco + SQLite real)
# --------------------------------------------------------------------------- #
class BaseBanco(unittest.TestCase):
    """Cria um banco novo (com os dados iniciais de demonstração) a cada teste."""

    def setUp(self):
        self.pasta = tempfile.mkdtemp()
        self.db = app.Banco(Path(self.pasta) / "teste.db")
        self.admin = app.Sessao("admin", self.db.autenticar("admin", "admin123"))
        self.estoquista = app.Sessao("estoque", self.db.autenticar("estoque", "estoque123"))

    def tearDown(self):
        self.db.con.close()
        shutil.rmtree(self.pasta, ignore_errors=True)

    def quantidade(self, isbn):
        return self.db.con.execute(
            "SELECT quantidade FROM livros WHERE isbn = ?", (isbn,)).fetchone()[0]

    def total_movimentacoes(self):
        return self.db.con.execute("SELECT COUNT(*) FROM movimentacoes").fetchone()[0]


class TestAutenticacao(BaseBanco):
    def test_login_correto_retorna_perfil(self):
        self.assertEqual(self.db.autenticar("admin", "admin123"), "admin")
        self.assertEqual(self.db.autenticar("  ESTOQUE ", "estoque123"), "estoquista")

    def test_senha_errada_ou_usuario_inexistente(self):
        self.assertIsNone(self.db.autenticar("admin", "errada"))
        self.assertIsNone(self.db.autenticar("fantasma", "admin123"))

    def test_senha_nao_e_guardada_em_texto_puro(self):
        linha = self.db.con.execute(
            "SELECT senha_hash FROM usuarios WHERE usuario = 'admin'").fetchone()
        self.assertNotIn(b"admin123", bytes(linha[0]))

    def test_criar_usuario_novo_e_redefinir_senha(self):
        self.db.criar_usuario("carla", "senha-forte-1", "estoquista")
        self.assertEqual(self.db.autenticar("carla", "senha-forte-1"), "estoquista")
        self.db.criar_usuario("carla", "outra-senha-2", "estoquista")
        self.assertIsNone(self.db.autenticar("carla", "senha-forte-1"))
        self.assertEqual(self.db.autenticar("carla", "outra-senha-2"), "estoquista")


class TestCadastro(BaseBanco):
    def test_cadastrar_e_consultar_livro(self):
        self.db.cadastrar_livro(self.admin, "9788535902775", "Livro X", "Autor Y", 4990, 5)
        livro = self.db.obter_livro(self.admin, "9788535902775")
        self.assertEqual((livro["titulo"], livro["preco_centavos"], livro["quantidade"]),
                         ("Livro X", 4990, 5))
        self.assertEqual(self.total_movimentacoes(), 1)  # o cadastro foi registrado

    def test_isbn_duplicado_gera_erro_de_negocio_no_campo_isbn(self):
        with self.assertRaises(app.ErroNegocio) as ctx:
            self.db.cadastrar_livro(self.admin, "9780000000011", "Outro", "Alguém", 1000, 1)
        self.assertEqual(ctx.exception.campo, "isbn")

    def test_estoquista_nao_pode_cadastrar(self):
        with self.assertRaises(app.ErroPermissao):
            self.db.cadastrar_livro(self.estoquista, "9780000000099", "X", "Y", 1000, 1)
        self.assertIsNone(self.db.obter_livro(self.admin, "9780000000099"))

    def test_atualizar_livro_nao_altera_quantidade(self):
        antes = self.quantidade("9780000000011")
        self.db.atualizar_livro(self.admin, "9780000000011", "Novo título", "Novo autor", 5555)
        livro = self.db.obter_livro(self.admin, "9780000000011")
        self.assertEqual((livro["titulo"], livro["preco_centavos"]), ("Novo título", 5555))
        self.assertEqual(livro["quantidade"], antes)

    def test_obter_livro_inexistente(self):
        self.assertIsNone(self.db.obter_livro(self.admin, "0000000000000"))


class TestMovimentacao(BaseBanco):
    ISBN = "9780000000011"  # Dom Casmurro, 12 exemplares nos dados de demonstração

    def test_entrada_soma_ao_estoque(self):
        livro = self.db.movimentar(self.estoquista, self.ISBN, "entrada", 8)
        self.assertEqual(livro["quantidade"], 20)
        self.assertEqual(self.quantidade(self.ISBN), 20)

    def test_saida_subtrai_do_estoque(self):
        livro = self.db.movimentar(self.estoquista, self.ISBN, "saida", 5)
        self.assertEqual(livro["quantidade"], 7)

    def test_saida_pode_zerar_o_estoque(self):
        self.db.movimentar(self.estoquista, self.ISBN, "saida", 12)
        self.assertEqual(self.quantidade(self.ISBN), 0)

    def test_saida_maior_que_o_estoque_e_recusada_sem_alterar_nada(self):
        movs_antes = self.total_movimentacoes()
        with self.assertRaises(app.ErroNegocio) as ctx:
            self.db.movimentar(self.estoquista, self.ISBN, "saida", 13)
        self.assertEqual(ctx.exception.campo, "quantidade")
        self.assertEqual(self.quantidade(self.ISBN), 12)
        self.assertEqual(self.total_movimentacoes(), movs_antes)

    def test_saida_de_livro_esgotado(self):
        with self.assertRaises(app.ErroNegocio) as ctx:
            self.db.movimentar(self.estoquista, "9780000000035", "saida", 1)  # O Cortiço: 0
        self.assertIn("esgotado", str(ctx.exception))

    def test_isbn_inexistente(self):
        with self.assertRaises(app.ErroNegocio) as ctx:
            self.db.movimentar(self.estoquista, "0000000000000", "entrada", 1)
        self.assertEqual(ctx.exception.campo, "isbn")

    def test_tipo_invalido(self):
        with self.assertRaises(ValueError):
            self.db.movimentar(self.estoquista, self.ISBN, "roubo", 1)

    def test_movimentacao_fica_registrada_com_usuario(self):
        self.db.movimentar(self.estoquista, self.ISBN, "entrada", 2)
        linha = self.db.con.execute(
            "SELECT tipo, quantidade, usuario FROM movimentacoes ORDER BY id DESC LIMIT 1"
        ).fetchone()
        self.assertEqual(tuple(linha), ("entrada", 2, "estoque"))

    def test_sequencia_de_operacoes_mantem_saldo_consistente(self):
        self.db.movimentar(self.admin, self.ISBN, "entrada", 10)   # 22
        self.db.movimentar(self.admin, self.ISBN, "saida", 7)      # 15
        self.db.movimentar(self.admin, self.ISBN, "saida", 15)     # 0
        self.assertEqual(self.quantidade(self.ISBN), 0)

    def test_banco_recusa_quantidade_negativa_mesmo_sem_a_regra_do_codigo(self):
        # a restrição CHECK do SQLite é a última linha de defesa
        with self.assertRaises(sqlite3.IntegrityError):
            self.db.con.execute("UPDATE livros SET quantidade = -1 WHERE isbn = ?", (self.ISBN,))


class TestConsulta(BaseBanco):
    def test_lista_todos_ordenados_por_titulo(self):
        linhas, total, _ = self.db.listar(self.admin)
        titulos = [l["titulo"] for l in linhas]
        self.assertEqual(total, len(linhas))
        self.assertEqual(titulos, sorted(titulos, key=str.casefold))

    def test_pesquisa_por_titulo_sem_acento(self):
        linhas, total, _ = self.db.listar(self.admin, "cortico")
        self.assertEqual([l["titulo"] for l in linhas], ["O Cortiço"])
        self.assertGreater(total, 1)

    def test_pesquisa_por_autor(self):
        linhas, _, _ = self.db.listar(self.admin, "clarice")
        self.assertEqual([l["titulo"] for l in linhas], ["A Hora da Estrela"])

    def test_pesquisa_por_isbn_parcial_com_hifen(self):
        linhas, _, _ = self.db.listar(self.admin, "978-000000002")
        self.assertEqual([l["titulo"] for l in linhas], ["Vidas Secas"])

    def test_pesquisa_sem_resultado(self):
        linhas, _, _ = self.db.listar(self.admin, "inexistente")
        self.assertEqual(linhas, [])

    def test_conta_livros_com_estoque_baixo_ou_zerado(self):
        # demonstração: Vidas Secas (3) e O Cortiço (0) estão em ou abaixo do limite
        _, _, baixos = self.db.listar(self.admin)
        self.assertEqual(baixos, 2)


class TestFluxoCompleto(BaseBanco):
    def test_cadastrar_movimentar_e_consultar(self):
        isbn = "9788535902775"
        self.db.cadastrar_livro(self.admin, isbn, "Livro de Teste", "Autora Teste", 2500, 2)
        self.db.movimentar(self.estoquista, isbn, "entrada", 10)
        self.db.movimentar(self.estoquista, isbn, "saida", 11)
        linhas, _, _ = self.db.listar(self.estoquista, "teste")
        self.assertEqual(len(linhas), 1)
        self.assertEqual(linhas[0]["quantidade"], 1)
        self.assertEqual(self.total_movimentacoes(), 3)  # cadastro + entrada + saída


if __name__ == "__main__":
    unittest.main(verbosity=2)