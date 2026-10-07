# -*- coding: utf-8 -*-
"""
===============================================================================
 ANALISADOR HARMÔNICO TONAL  —  Python 3 / Google Colab
===============================================================================
 Entrada : progressão de acordes em cifra, separados por espaço
           (ex.: "Cmaj7 A7 Dm7 G7 Cmaj7 Fm6 Bb7 Cmaj7")
 Saída   : tonalidade (com detecção de modulações e acordes pivô), grau em
           algarismos romanos (com inversões), função tonal, classificação
           (diatônico, empréstimo modal, dominante secundária, dominante
           substituto/trítono, ii–V secundário, sensível secundária,
           napolitano, cromático), escala do tom, escala do acorde,
           cadências e campos harmônicos (maior, maior harmônico, menor
           natural, menor harmônica e menor melódica).

 COMO O ALGORITMO FUNCIONA
 1) Cada cifra vira um objeto Acorde (terça, quinta, sétima, extensões,
    alterações, baixo/inversão).
 2) Para CADA uma das 24 tonalidades (12 maiores + 12 menores) e CADA acorde,
    o programa gera todas as leituras possíveis (diatônico, empréstimo modal,
    dominante secundário, V7 substituto, ii–V, vii° secundário, napolitano,
    cromático) e dá uma pontuação a cada leitura.
 3) Um algoritmo de Viterbi escolhe a SEQUÊNCIA de tonalidades de maior
    pontuação total, cobrando uma "multa" a cada mudança de tom (menor para
    tons vizinhos). Excursões curtas viram dominantes secundários/empréstimos;
    permanências longas viram modulação.
 4) Pós-processamento: acorde pivô, cadências, ii–V, escalas e campos
    harmônicos.
===============================================================================
"""
import re
import html as _html
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Tuple

# =============================================================================
# 1. TABELAS BÁSICAS
# =============================================================================
LETRAS = "CDEFGAB"
PC_NATURAL = {"C": 0, "D": 2, "E": 4, "F": 5, "G": 7, "A": 9, "B": 11}
SOLFEJO = {"C": "Dó", "D": "Ré", "E": "Mi", "F": "Fá", "G": "Sol", "A": "Lá", "B": "Si"}
ACID_DIFF = {0: "", 1: "#", 2: "##", 11: "b", 10: "bb"}
NOMES_MAIOR = ["C", "Db", "D", "Eb", "E", "F", "F#", "G", "Ab", "A", "Bb", "B"]
NOMES_MENOR = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "G#", "A", "Bb", "B"]
ROMANOS = ["I", "II", "III", "IV", "V", "VI", "VII"]

# Escalas (intervalos em semitons a partir da tônica)
ESCALAS: Dict[str, List[int]] = {
    "maior": [0, 2, 4, 5, 7, 9, 11],
    "menor natural": [0, 2, 3, 5, 7, 8, 10],
    "menor harmônica": [0, 2, 3, 5, 7, 8, 11],
    "menor melódica": [0, 2, 3, 5, 7, 9, 11],
    "maior harmônico": [0, 2, 4, 5, 7, 8, 11],
    "maior melódico": [0, 2, 4, 5, 7, 8, 10],
    "dórico": [0, 2, 3, 5, 7, 9, 10],
    "frígio": [0, 1, 3, 5, 7, 8, 10],
    "lídio": [0, 2, 4, 6, 7, 9, 11],
    "mixolídio": [0, 2, 4, 5, 7, 9, 10],
    "lócrio": [0, 1, 3, 5, 6, 8, 10],
    "lídio b7": [0, 2, 4, 6, 7, 9, 10],
}
SETS = {k: frozenset(v) for k, v in ESCALAS.items()}
ESCALA_LONGA = {
    "maior": "maior (jônio)",
    "menor natural": "menor natural (eólio)",
    "maior melódico": "maior melódico (mixolídio ♭6)",
    "lídio b7": "lídio ♭7 (lídio dominante)",
}


def esc_longa(nome: str) -> str:
    return ESCALA_LONGA.get(nome, nome)


# Modos de cada escala (nomes no padrão do mDecks/Tessitura) e tradução para PT
_MODOS_MAIOR = ["Ionian", "Dorian", "Phrygian", "Lydian", "Mixo.", "Aeolian", "Locrian"]
_MODOS_HARM = ["Harmonic Minor", "Locrian n13", "Ionian #5", "Dorian #4", "Mixo. b9 b13",
               "Lydian #2", "Alt.Dom.o7"]
_MODOS_MELO = ["Mel. min", "Dorian b2", "Lydian #5", "Lydian b7", "Mixo. b13", "Locrian n9", "Alt."]
_MODOS_HMAIOR = ["Harmonic Major", "Dorian b5", "Phrygian b4", "Lydian b3", "Mixo. b2",
                 "Lydian #2 #5", "Locrian bb7"]
_ROT = {
    "maior": (_MODOS_MAIOR, 0), "dórico": (_MODOS_MAIOR, 1), "frígio": (_MODOS_MAIOR, 2),
    "lídio": (_MODOS_MAIOR, 3), "mixolídio": (_MODOS_MAIOR, 4),
    "menor natural": (_MODOS_MAIOR, 5), "lócrio": (_MODOS_MAIOR, 6),
    "menor harmônica": (_MODOS_HARM, 0), "menor melódica": (_MODOS_MELO, 0),
    "lídio b7": (_MODOS_MELO, 3), "maior melódico": (_MODOS_MELO, 4),
    "maior harmônico": (_MODOS_HMAIOR, 0),
}
PT_ESCALA = {
    "Ionian": "jônio", "Dorian": "dórico", "Phrygian": "frígio", "Lydian": "lídio",
    "Mixo.": "mixolídio", "Aeolian": "eólio", "Locrian": "lócrio",
    "Harmonic Minor": "menor harmônica", "Locrian n13": "lócrio ♮13 (lócrio ♮6)",
    "Ionian #5": "jônio ♯5", "Dorian #4": "dórico ♯4", "Mixo. b9 b13": "mixolídio ♭9 ♭13 (frígio dominante)",
    "Lydian #2": "lídio ♯2", "Alt.Dom.o7": "dominante alterada diminuta (7º modo da menor harmônica)",
    "Mel. min": "menor melódica", "Dorian b2": "dórico ♭2", "Lydian #5": "lídio ♯5",
    "Lydian b7": "lídio ♭7 (lídio dominante)", "Mixo. b13": "mixolídio ♭13", "Locrian n9": "lócrio ♮9",
    "Alt.": "alterada (super-lócrio)", "Harmonic Major": "maior harmônico", "Dorian b5": "dórico ♭5",
    "Phrygian b4": "frígio ♭4", "Lydian b3": "lídio ♭3", "Mixo. b2": "mixolídio ♭2",
    "Lydian #2 #5": "lídio ♯2 ♯5", "Locrian bb7": "lócrio ♭♭7", "Dim.": "diminuta (tom–semitom)",
    "Hexa. IV:Vm": "hexatônica IV:Vm (sus4 sobre dominante maior)",
    "Hexa. IV:Vo": "hexatônica IV:Vo (sus4 com ♭9, alvo menor)",
}


def nome_modo(escala: str, idx: int) -> str:
    lista, off = _ROT[escala]
    return lista[(off + idx) % 7]


def fmt_escala(raiz: str, en: str) -> str:
    return f"{raiz} {PT_ESCALA.get(en, en)} ({en})" if en else ""


# Escalas "da casa" (diatônicas) e escalas das quais se pode pedir empréstimo
PRIMARIAS = {
    "maior": [("maior", 3.0)],
    "menor": [("menor natural", 3.0), ("menor harmônica", 2.7), ("menor melódica", 2.3)],
}
EMPRESTIMO = {
    "maior": [("menor natural", 1.9), ("mixolídio", 1.7), ("menor harmônica", 1.7),
              ("dórico", 1.6), ("lídio", 1.6), ("maior harmônico", 1.6),
              ("maior melódico", 1.6), ("frígio", 1.5), ("menor melódica", 1.5),
              ("lócrio", 1.2)],
    "menor": [("maior", 1.9), ("dórico", 1.8), ("mixolídio", 1.5), ("lídio", 1.5),
              ("maior harmônico", 1.5), ("frígio", 1.5), ("lócrio", 1.2),
              ("maior melódico", 1.2)],
}
PRIORIDADE_ESCALA = {
    "maior": ["maior", "mixolídio", "lídio", "dórico", "menor natural", "maior harmônico",
              "menor harmônica", "menor melódica", "frígio", "maior melódico", "lócrio", "lídio b7"],
    "menor": ["menor natural", "menor harmônica", "menor melódica", "dórico", "frígio", "maior",
              "mixolídio", "lídio", "lócrio", "maior harmônico", "maior melódico", "lídio b7"],
}

# Grau (acidente, número) de cada semitom em relação à tônica. Como no mDecks, também em
# tom menor usa-se a grafia relativa à escala maior (♭III, ♭VI, ♭VII).
GRAUS = {
    "maior": {0: ("", 1), 1: ("♭", 2), 2: ("", 2), 3: ("♭", 3), 4: ("", 3), 5: ("", 4),
              6: ("♯", 4), 7: ("", 5), 8: ("♭", 6), 9: ("", 6), 10: ("♭", 7), 11: ("", 7)},
}
GRAUS["menor"] = GRAUS["maior"]
# Graus que podem ser "tonicizados" (alvos de dominantes/ii–V secundários).
# deslocamento -> (rótulo em maiúsculas, é_empréstimo_modal?)
ALVOS = {
    "maior": {2: ("II", False), 4: ("III", False), 5: ("IV", False), 7: ("V", False),
              9: ("VI", False), 3: ("♭III", True), 8: ("♭VI", True), 10: ("♭VII", True)},
    "menor": {3: ("♭III", False), 5: ("IV", False), 7: ("V", False), 8: ("♭VI", False),
              10: ("♭VII", False)},
}
FUNCAO = {
    "maior": {0: "Tônica", 1: "Subdominante", 2: "Subdominante", 3: "Tônica", 4: "Tônica",
              5: "Subdominante", 6: "Dominante", 7: "Dominante", 8: "Subdominante",
              9: "Tônica", 10: "Subdominante", 11: "Dominante"},
    "menor": {0: "Tônica", 1: "Subdominante", 2: "Subdominante", 3: "Tônica", 4: "Tônica",
              5: "Subdominante", 6: "Dominante", 7: "Dominante", 8: "Subdominante",
              9: "Subdominante", 10: "Dominante (subtônica)", 11: "Dominante"},
}


# =============================================================================
# 2. NOTAS, TONALIDADES E NOMES
# =============================================================================
def pc_de_nome(nome: str) -> int:
    return (PC_NATURAL[nome[0].upper()] + nome.count("#") - nome.count("b")) % 12


def _armadura(nome: str) -> int:
    base = {"F": -1, "C": 0, "G": 1, "D": 2, "A": 3, "E": 4, "B": 5}[nome[0]]
    return base + 7 * (nome.count("#") - nome.count("b"))


def nome_tonica(tom: Tuple[int, str], hints: Dict[int, str]) -> str:
    """Nome (cifra) da tônica; usa a grafia que o usuário digitou, se sensata."""
    t, modo = tom
    padrao = (NOMES_MAIOR if modo == "maior" else NOMES_MENOR)[t]
    h = hints.get(t)
    if h:
        arm = _armadura(h) - (3 if modo == "menor" else 0)
        if abs(arm) <= 7:
            return h
    return padrao


def nome_tom(tom, hints) -> str:
    n = nome_tonica(tom, hints)
    solf = SOLFEJO[n[0]] + n[1:].replace("#", "♯").replace("b", "♭")
    return f"{solf} {tom[1]} ({n}{'m' if tom[1] == 'menor' else ''})"


def cifra_tom(tom, hints) -> str:
    return nome_tonica(tom, hints) + ("m" if tom[1] == "menor" else "")


def soletrar_escala(tonica: str, intervalos: List[int]) -> List[str]:
    """Escreve a escala com grafia correta (uma letra por grau)."""
    l0, pc0 = LETRAS.index(tonica[0]), pc_de_nome(tonica)
    saida = []
    for k, iv in enumerate(intervalos):
        letra = LETRAS[(l0 + k) % 7]
        diff = ((pc0 + iv) - PC_NATURAL[letra]) % 12
        saida.append(letra + ACID_DIFF.get(diff, "?"))
    return saida


def nome_nota_rel(rel: int, tom, hints) -> str:
    """Nome da nota situada 'rel' semitons acima da tônica, grafada pelo grau."""
    t, modo = tom
    tn = nome_tonica(tom, hints)
    _, d = GRAUS[modo][rel]
    letra = LETRAS[(LETRAS.index(tn[0]) + d - 1) % 7]
    diff = ((t + rel) - PC_NATURAL[letra]) % 12
    return letra + ACID_DIFF.get(diff, "?")


# =============================================================================
# 3. O ACORDE: PARSER DE CIFRAS
# =============================================================================
@dataclass
class Acorde:
    simbolo: str
    raiz: int
    nome_raiz: str
    baixo: int
    nome_baixo: str
    terca: Optional[int]
    quinta: Optional[int]
    setima: Optional[int]
    sus: Optional[int]
    ext_num: int
    adds: List[str]
    alts: List[str]
    core_rel: frozenset      # notas estruturais (relativas à raiz)
    ext_rel: frozenset       # extensões/alterações (9ª, 11ª, 13ª...)
    pcs_abs: frozenset       # todas as classes de altura (absolutas)

    def inversao(self) -> Optional[int]:
        b = (self.baixo - self.raiz) % 12
        if b == 0:
            return 0
        if self.terca is not None and b == self.terca:
            return 1
        if self.quinta is not None and b == self.quinta:
            return 2
        if self.setima is not None and b == self.setima:
            return 3
        return None

    @property
    def dim_triade(self):
        return self.terca == 3 and self.quinta == 6 and self.setima is None

    @property
    def dim7(self):
        return self.terca == 3 and self.quinta == 6 and self.setima == 9

    @property
    def meio_dim(self):
        return self.terca == 3 and self.quinta == 6 and self.setima == 10

    @property
    def menor7(self):
        return self.terca == 3 and self.quinta == 7 and self.setima == 10


_TOK = re.compile(r"(add\d+|sus2|sus4|sus|omit\d+|no\d+|alt|-5|-9|\+5|\+9|\+11|b13|b11|b9|b5|b6|"
                  r"#11|#9|#5|69|13|11|9|7|6|5|4|\+)")
_RAIZ = re.compile(r"^([A-Ga-g])(#{1,2}|b{1,2}|)(.*)$")


def parse_acorde(simbolo: str) -> Acorde:
    original = simbolo.strip()
    s = (original.replace("♯", "#").replace("♭", "b").replace("−", "-").replace("–", "-"))
    s = re.sub(r"[Δ△](?=\d)", "maj", s)
    s = re.sub(r"[Δ△]", "maj7", s)
    s = s.replace("ø7", "m7b5").replace("ø", "m7b5").replace("°", "dim").replace("º", "dim")
    s = s.replace("6/9", "69")
    baixo_txt = None
    if "/" in s:
        s, baixo_txt = s.split("/", 1)
    m = _RAIZ.match(s)
    if not m:
        raise ValueError(f"Não consegui ler o acorde '{original}'.")
    letra, acid, q = m.group(1).upper(), m.group(2), m.group(3)
    nome_raiz = letra + acid
    raiz = pc_de_nome(nome_raiz)

    q = re.sub(r"7M(?!aj)", "maj7", q).replace("7(4)", "7sus4")
    q = re.sub(r"[()\s,]", "", q)

    terca, quinta, setima, sus = 4, 7, None, None
    exts: List[int] = []
    adds: List[str] = []
    alts: List[str] = []
    ext_num = 0
    maj_flag = dim_flag = False

    for pat, tag in [(r"(?:min|mi|m|-)(?:maj|Maj|MAJ|M)(?=\d)", "mM"),
                     (r"(?:maj|Maj|MAJ|M)", "maj"),
                     (r"(?:dim|o(?=\d|$))", "dim"),
                     (r"(?:aug|\+)", "aug"),
                     (r"(?:min|mi|m|-)", "min")]:
        mm = re.match(pat, q)
        if mm:
            q = q[mm.end():]
            if tag == "mM":
                terca, setima, maj_flag = 3, 11, True
            elif tag == "maj":
                maj_flag = bool(q and q[0].isdigit())
            elif tag == "dim":
                terca, quinta, dim_flag = 3, 6, True
            elif tag == "aug":
                quinta = 8
            else:
                terca = 3
            break

    def sete_base():
        return 11 if maj_flag else (9 if dim_flag else 10)

    pos = 0
    while pos < len(q):
        tm = _TOK.match(q, pos)
        if not tm:
            raise ValueError(f"Não reconheci '{q[pos:]}' no acorde '{original}'.")
        tok, pos = tm.group(0), tm.end()
        if tok == "7":
            if setima is None:
                setima = sete_base()
        elif tok in ("9", "11", "13"):
            if setima is None:
                setima = sete_base()
            ext_num = max(ext_num, int(tok))
            exts += [14] + ([17] if tok == "11" else [21] if tok == "13" else [])
        elif tok == "6":
            adds.append("add6"); exts.append(9)
        elif tok == "69":
            adds.append("6/9"); exts += [9, 14]
        elif tok == "5":
            terca = None
        elif tok in ("4", "sus4", "sus"):
            terca, sus = None, 5
        elif tok == "sus2":
            terca, sus = None, 2
        elif tok.startswith("add"):
            mp = {2: 2, 4: 5, 6: 9, 9: 14, 11: 17, 13: 21}
            n = int(tok[3:])
            if n not in mp:
                raise ValueError(f"Extensão '{tok}' não suportada em '{original}'.")
            adds.append(tok); exts.append(mp[n])
        elif tok in ("b5", "-5"):
            quinta = 6; alts.append("b5")
        elif tok in ("#5", "+5", "+"):
            quinta = 8; alts.append("#5") if tok != "+" else None
        elif tok in ("b9", "-9"):
            exts.append(13); alts.append("b9")
        elif tok in ("#9", "+9"):
            exts.append(15); alts.append("#9")
        elif tok in ("#11", "+11"):
            exts.append(18); alts.append("#11")
        elif tok in ("b13", "b6"):
            exts.append(20); alts.append("b13")
        elif tok == "b11":
            exts.append(16); alts.append("b11")
        elif tok.startswith(("omit", "no")):
            n = int(re.sub(r"\D", "", tok))
            if n == 3:
                terca = None
            elif n == 5:
                quinta = None
        elif tok == "alt":
            if setima is None:
                setima = 10
            quinta = None
            exts += [13, 15, 18, 20]; alts.append("alt")

    core = frozenset(x % 12 for x in (0, terca, quinta, setima, sus) if x is not None)
    ext_rel = frozenset(e % 12 for e in exts) - core
    pcs_abs = frozenset((raiz + x) % 12 for x in (core | ext_rel))

    baixo, nome_baixo = raiz, nome_raiz
    if baixo_txt:
        mb = re.match(r"^([A-Ga-g])(#{1,2}|b{1,2}|)$", baixo_txt)
        if not mb:
            raise ValueError(f"Baixo inválido em '{original}'.")
        nome_baixo = mb.group(1).upper() + mb.group(2)
        baixo = pc_de_nome(nome_baixo)

    return Acorde(original, raiz, nome_raiz, baixo, nome_baixo, terca, quinta, setima, sus,
                  ext_num, adds, alts, core, ext_rel, pcs_abs)


def separar_progressao(texto: str) -> List[str]:
    saida = []
    for tk in texto.split():
        t = tk.strip("|,;")
        if not t or re.fullmatch(r"[-–—>→/\\|]+", t) or t.upper() in ("N.C.", "NC", "%"):
            continue
        saida.append(t)
    return saida


# =============================================================================
# 4. NUMERAIS ROMANOS
# =============================================================================
def sufixo(ch: Acorde, inv: Optional[int]) -> str:
    """Sufixo do numeral no estilo jazz/mDecks: △ (maj7), 7, 7b5, °7, +7, 7sus4 e inversões."""
    th, fi, se = ch.terca, ch.quinta, ch.setima
    fig3 = {1: "6", 2: "64"}
    fig4 = {1: "65", 2: "43", 3: "42"}
    if se is None:
        if th is None and ch.sus is None:
            s = "5"
        elif th == 3 and fi == 6:
            s = "°"
        elif th == 4 and fi == 8:
            s = "+"
        else:
            s = ""
        s += fig3.get(inv, "")
    elif se == 11:                       # maj7 (a sétima some nas inversões, como no mDecks)
        s = fig3[inv] if inv in (1, 2) else ("42" if inv == 3 else ("+△" if fi == 8 else "△"))
    elif inv in (1, 2, 3):
        s = ("°" if se == 9 else "") + fig4[inv]
    elif se == 9:
        s = "°7"
    elif (th == 3 and fi == 6) or (th == 4 and fi == 6):
        s = "7b5"
    elif th == 4 and fi == 8:
        s = "+7"
    else:
        s = "7"
    if ch.sus:
        s += "sus4" if ch.sus == 5 else "sus2"
    return s


def inv_efetiva(ch: Acorde) -> Tuple[int, bool]:
    """(inversão, pedal?). Baixo fora do acorde, na 7ª, ou na 5ª de m7 => ponto pedal (pp)."""
    inv = ch.inversao()
    if inv is None or inv == 3 or (inv == 2 and ch.menor7):
        return 0, True
    return inv, False


def numeral(base: str, ch: Acorde, inv: Optional[int] = 0) -> str:
    inv_e, pp = inv_efetiva(ch)
    b = base.lower() if (ch.terca == 3 and not ch.dim7) else base.upper()
    return "pp" + b if pp else b + sufixo(ch, inv_e)


def numeral_sec(base: str, ch: Acorde, alvo: str = "") -> str:
    """Numeral de função secundária: base ('V','ii','VII','subV') + qualidade + '/alvo'."""
    inv_e, pp = inv_efetiva(ch)
    corpo = base if pp else base + sufixo(ch, inv_e)
    return ("pp" if pp else "") + corpo + (("/" + alvo) if alvo else "")


def base_romana(rel: int, modo: str) -> str:
    acid, d = GRAUS["maior"][rel]
    return acid + ROMANOS[d - 1]


# =============================================================================
# 5. INTERPRETAÇÃO DE UM ACORDE DENTRO DE UMA TONALIDADE
# =============================================================================
@dataclass
class Interp:
    score: float
    tipo: str            # diatonico | emprestimo | dom_sec | sub_dom | ii_sec | dim_sec | napolitano | cromatico
    grau: str
    escala: str = ""
    alvo_pc: Optional[int] = None
    alvo_rot: str = ""
    nota: str = ""
    funcao: str = ""
    esc_acorde: str = ""
    alternativas: List[str] = field(default_factory=list)


def eh_dominante(ch: Acorde) -> bool:
    """Acorde de função dominante: tríade maior, 7ª da dominante ou 7sus4."""
    if ch.setima not in (None, 10) or ch.quinta not in (7, 6, 8, None):
        return False
    if ch.terca == 4:
        return True
    return ch.terca is None and ch.sus == 5 and ch.setima == 10


def eh_dom7(ch: Acorde) -> bool:
    return eh_dominante(ch) and ch.setima == 10


def eh_estavel(ch: Acorde) -> bool:
    return not eh_dom7(ch)


def qualidade_tonica(ch: Acorde, modo: str, ultimo: bool) -> bool:
    if ch.quinta not in (7, None):
        return False
    if modo == "maior":
        return ch.terca in (4, None)
    return ch.terca in (3, None) or (ultimo and ch.terca == 4)  # terça de Picardia


def nucleo_efetivo(ch: Acorde):
    """Notas estruturais; no 7sus4 a 4ª é lida como a 3ª maior (função de dominante)."""
    core = ch.core_rel
    if ch.sus == 5 and ch.setima == 10:
        core = frozenset(4 if x == 5 else x for x in core)
    if ch.setima == 10 and ch.quinta in (6, 8) and (ch.terca == 4 or ch.sus):
        core = frozenset(x for x in core if x != ch.quinta)     # 7b5 / 7#5: quinta alterada é tensão
    return core


def casa_com_escala(ch: Acorde, rel: int, escala: str) -> bool:
    """O acorde é (ou é um recorte de) o acorde formado por terças empilhadas sobre aquele grau?"""
    iv = ESCALAS[escala]
    if rel not in iv:
        return False
    k = iv.index(rel)
    t3 = (iv[(k + 2) % 7] - iv[k]) % 12
    t5 = (iv[(k + 4) % 7] - iv[k]) % 12
    t7 = (iv[(k + 6) % 7] - iv[k]) % 12
    terca = 4 if (ch.sus == 5 and ch.setima == 10) else ch.terca
    if terca is not None and terca != t3:
        return False
    alterada = ch.setima == 10 and ch.quinta in (6, 8) and (ch.terca == 4 or ch.sus)
    if ch.quinta is not None and not alterada and ch.quinta != t5:
        return False
    if ch.setima is not None and ch.setima != t7:
        return False
    return True


def explicado_no_tom(ch: Acorde, tom: Tuple[int, str]) -> Optional[str]:
    """'diatonico' (campo do tom), 'emprestimo' (modo homônimo usual) ou None (fora do tom)."""
    t, modo = tom
    rel = (ch.raiz - t) % 12
    core = {(rel + x) % 12 for x in nucleo_efetivo(ch)}
    if any(core <= SETS[nome] and casa_com_escala(ch, rel, nome) for nome, _ in PRIMARIAS[modo]):
        return "diatonico"
    if any(core <= SETS[nome] and casa_com_escala(ch, rel, nome) for nome, sc in EMPRESTIMO[modo]
           if sc >= 1.7 and not (modo == "menor" and nome == "maior" and ch.setima == 11 and rel != 0)):
        return "emprestimo"
    return None


def cadeia_dominantes(acordes: List[Acorde], i: int):
    """Cadeia de dominantes (7ª) em quintas descendentes a partir de i.
    Retorna (índices da cadeia, índice do acorde de destino ou None)."""
    n = len(acordes)
    cadeia = [i]
    if not eh_dom7(acordes[i]):
        return cadeia, None
    j = i
    while j + 1 < n and eh_dom7(acordes[j + 1]) and acordes[j + 1].raiz == (acordes[j].raiz + 5) % 12:
        j += 1
        cadeia.append(j)
    dest = j + 1 if j + 1 < n and acordes[j + 1].raiz == (acordes[j].raiz + 5) % 12 else None
    return cadeia, dest


def cands_dominante(ch: Acorde, tom, i: int, acordes: List[Acorde], diat: Optional["Interp"],
                    final: bool = False):
    """Regras para dominantes: resolve em acorde do campo => secundário/estendido;
    resolve em acorde fora do campo e que não é empréstimo => dominante de modulação."""
    n = len(acordes)
    t, modo = tom
    alvos = ALVOS[modo]
    nxt = acordes[i + 1] if i + 1 < n else None
    rel = (ch.raiz - t) % 12
    out: List[Interp] = []
    if not eh_dominante(ch):
        return out
    base7 = 2.0 if ch.setima == 10 else 1.8

    def mk(sc, rot, troot, nota, tipo="dom_sec", grau=None):
        if ch.setima is None:
            sc = min(sc, 2.25)
        return Interp(sc, tipo, grau or numeral_sec("V", ch, rot), alvo_pc=troot, alvo_rot=rot, nota=nota)

    resolve = nxt is not None and nxt.raiz == (ch.raiz + 5) % 12
    if not resolve:                      # dominante "solto": só alvos do campo
        for off, (rot, emp) in alvos.items():
            if not emp and ch.raiz == (t + off + 7) % 12:
                extra = 0.5 if (nxt is not None and nxt.raiz == ch.raiz and nxt.terca == 3) else 0.0
                if rot == "V" and ch.setima == 10:
                    extra += 0.5
                if rel == 0 and ch.setima == 10:
                    extra += 0.6
                out.append(mk(base7 + extra, rot, (t + off) % 12,
                              f"Dominante secundário de {rot} (resolução esperada não ocorre de imediato)"))
        return out
    off_t = (nxt.raiz - t) % 12
    if off_t == 0:
        return out                       # V→I primário: tratado como diatônico/empréstimo
    troot = nxt.raiz
    emp = off_t in alvos and alvos[off_t][1]
    expl = explicado_no_tom(nxt, tom)
    rot = alvos[off_t][0] if off_t in alvos else base_romana(off_t, modo)
    boost = diat is not None and ch.setima == 10 and rel != 7 and not emp

    def sec(extra=""):
        sc = base7 + 0.9 - (0.2 if emp else 0.0)
        if boost and final:
            sc = max(sc, diat.score + 0.2)
        return mk(sc, rot, troot, f"Dominante secundário de {rot}: resolve em {nxt.simbolo}" + extra)

    def modulacao():
        alvo_c = nxt.nome_raiz + ("m" if nxt.terca == 3 else "")
        it = mk(0.8, alvo_c, troot,
                f"Dominante do novo tom: resolve em {nxt.simbolo}, fora do campo e sem ser empréstimo "
                f"modal; indica modulação para {alvo_c}", tipo="dom_mod")
        return it

    if eh_dom7(nxt):                     # cadeia de dominantes
        if emp:
            return out
        cadeia, dest = cadeia_dominantes(acordes, i)
        dest_ok = dest is not None and explicado_no_tom(acordes[dest], tom) is not None
        if expl is None and not dest_ok and not (off_t in alvos and not emp):
            out.append(modulacao())
        elif off_t in alvos:
            out.append(sec(" (cadeia de dominantes)"))
        elif len(cadeia) >= 2 and dest_ok:
            d_off = (acordes[dest].raiz - t) % 12
            niv = len(cadeia)
            tail = "/V" * (niv - 1)
            rot_d = "I"
            if d_off != 0:
                rot_d = alvos[d_off][0] if d_off in alvos else base_romana(d_off, modo)
                tail += "/" + rot_d
            it = mk(2.8, rot_d, acordes[dest].raiz, f"Dominante estendido: a cadeia de dominantes chega em "
                    f"{acordes[dest].simbolo} ({rot_d}), que pertence ao campo harmônico", tipo="dom_est",
                    grau=numeral_sec("V", ch, "") + tail)
            out.append(it)
        else:
            out.append(sec())
    else:
        if expl is None:
            out.append(modulacao())
        else:
            out.append(sec(" (acorde de empréstimo modal)" if expl == "emprestimo" and not emp else ""))
    return out


def interpretar(ch: Acorde, tom: Tuple[int, str], i: int, acordes: List[Acorde],
                final: bool = False) -> Interp:
    """final=False: pontuação usada para DECIDIR o tom (neutra).
    final=True: pontuação usada para ESCOLHER o rótulo no tom já decidido (prefere ii–V/V7 secundários)."""
    n = len(acordes)
    t, modo = tom
    nxt = acordes[i + 1] if i + 1 < n else None
    nxt2 = acordes[i + 2] if i + 2 < n else None
    rel = (ch.raiz - t) % 12
    core = {(rel + x) % 12 for x in nucleo_efetivo(ch)}
    exts = {(rel + x) % 12 for x in ch.ext_rel}
    rel_nxt = (nxt.raiz - t) % 12 if nxt else None
    alvos = ALVOS[modo]
    cands: List[Interp] = []

    # ---- bônus contextuais (tônica e cadência) -------------------------------
    bonus = 0.0
    if rel == 0 and qualidade_tonica(ch, modo, i == n - 1):
        pen7 = ch.setima == 10
        bonus += (0.2 if pen7 else 0.4)
        bonus += (0.4 if pen7 else 0.9) if i == 0 else 0
        bonus += (0.4 if pen7 else 1.8) if i == n - 1 else 0
    if rel_nxt == 0 and nxt is not None:
        if rel == 7 and (ch.terca == 4 or eh_dom7(ch)):
            bonus += 1.2
        elif rel == 11 and (ch.dim_triade or ch.dim7 or ch.meio_dim):
            bonus += 0.6

    if (rel == 0 and i > 0 and qualidade_tonica(ch, modo, i == n - 1)
            and (acordes[i - 1].raiz - t) % 12 == 7 and eh_dominante(acordes[i - 1])):
        bonus += 0.5                      # pouso da cadência V→I

    pouso = (i > 0 and eh_dom7(acordes[i - 1]) and acordes[i - 1].raiz == (ch.raiz + 7) % 12
             and eh_estavel(ch))
    if pouso and rel != 0:
        bonus += 0.8                      # pouso de dominante secundário em grau do campo

    rom = numeral(base_romana(rel, modo), ch)

    # ---- 1) diatônico (campo harmônico do tom) -------------------------------
    diat = None
    for nome, sc in PRIMARIAS[modo]:
        if core <= SETS[nome] and casa_com_escala(ch, rel, nome):
            pen = 0.15 * len([e for e in exts if e not in SETS[nome]])
            diat = Interp(sc - pen + bonus, "diatonico", rom, escala=nome)
            break
    if diat:
        cands.append(diat)

    # ---- 2) empréstimo modal -------------------------------------------------
    if not diat:
        achados = [(sc, nome) for nome, sc in EMPRESTIMO[modo]
                   if core <= SETS[nome] and casa_com_escala(ch, rel, nome)
                   and not (modo == "menor" and nome == "maior" and ch.setima == 11 and rel != 0)]
        if achados:
            achados.sort(key=lambda x: -x[0])
            sc, nome = achados[0]
            pen = 0.15 * len([e for e in exts if e not in SETS[nome]])
            b_ = bonus if (sc >= 1.7 or not (pouso and rel != 0)) else bonus - 0.8
            it = Interp(sc - pen + b_, "emprestimo", rom, escala=nome)
            outros = [esc_longa(nm) for _, nm in achados[1:4]]
            it.nota = f"Empréstimo modal: acorde da escala {esc_longa(nome)} da tônica homônima"
            if outros:
                it.nota += " (também presente em: " + ", ".join(outros) + ")"
            if modo == "menor" and rel == 0 and ch.terca == 4 and i == n - 1:
                it.nota = "Tônica maior em tom menor: terça de Picardia"
            if modo == "maior" and rel == 10 and ch.setima == 10 and rel_nxt == 0:
                it.nota += ". ♭VII7→I = dominante 'backdoor'"
            cands.append(it)

    # ---- 3) dominantes: secundário / estendido / de modulação ----------------
    dom = cands_dominante(ch, tom, i, acordes, diat, final)
    cands += dom
    if any(c.tipo == "dom_mod" for c in dom):
        for c in cands:
            if c.tipo == "emprestimo":
                c.score -= 0.6

    # ---- 4) V7 substituto (trítono) ------------------------------------------
    if ch.terca == 4 and ch.setima == 10 and ch.quinta in (7, 6, 8, None):
        for off, rot in [(0, "")] + [(o, v[0]) for o, v in alvos.items() if not v[1]]:
            troot = (t + off) % 12
            if ch.raiz != (troot + 1) % 12:
                continue
            res = nxt is not None and nxt.raiz == troot
            alvo_txt = rot or "I"
            it = Interp(2.4 if res else 1.5, "sub_dom", numeral_sec("subV", ch, rot),
                        alvo_pc=troot, alvo_rot=alvo_txt)
            it.nota = (f"Dominante substituto (trítono) de V7/{alvo_txt}: mesmo trítono, resolve por "
                       f"semitom descendente em {nxt.simbolo}" if res else
                       f"Dominante substituto (trítono) de V7/{alvo_txt} (resolução não imediata)")
            if off == 7:
                it.nota += ". Enarmônico à sexta aumentada alemã (Ger+6) resolvendo em V"
            cands.append(it)

    # ---- 5) diminutos --------------------------------------------------------
    if ch.dim7 and nxt is not None:
        achou = False
        if (ch.raiz + 1) % 12 == nxt.raiz and rel_nxt in alvos:       # sensível pela grafia
            rot = alvos[rel_nxt][0]
            cands.append(Interp(2.6, "dim_sec", numeral_sec("VII", ch, rot), alvo_pc=nxt.raiz,
                                alvo_rot=rot, nota=f"Diminuto de sensível: resolve em {nxt.simbolo} ({rot})"))
            achou = True
        if (ch.raiz - 1) % 12 == nxt.raiz:                             # passagem descendente
            cands.append(Interp(2.6, "dim_pass", numeral(base_romana(rel, modo), ch),
                                nota=f"Diminuto de passagem: desce por semitom até {nxt.simbolo}"))
            achou = True
        if not achou:
            for off, (rot, emp) in alvos.items():
                troot = (t + off) % 12
                if nxt.raiz == troot and (troot - 1) % 12 in ch.pcs_abs:
                    cands.append(Interp(2.3, "dim_sec", numeral_sec("VII", ch, rot), alvo_pc=troot,
                                        alvo_rot=rot, nota=f"Diminuto de sensível de {rot}: resolve em {nxt.simbolo}"))
    if ch.dim_triade or ch.meio_dim:
        for off, (rot, emp) in alvos.items():
            troot = (t + off) % 12
            if ch.raiz == (troot - 1) % 12 and not (ch.meio_dim and nxt is not None and eh_dominante(nxt)
                                                      and nxt.raiz == (ch.raiz + 5) % 12):
                res = nxt is not None and nxt.raiz == troot
                cands.append(Interp(2.3 if res else 1.5, "dim_sec", numeral_sec("vii", ch, rot),
                                    alvo_pc=troot, alvo_rot=rot,
                                    nota=f"Acorde de sensível secundário de {rot}"
                                         + (f": resolve em {nxt.simbolo}" if res else " (sem resolução imediata)")))

    # ---- 6) ii–V secundário (e subii–subV) -----------------------------------
    if (ch.terca == 3 and ch.setima == 10 and ch.quinta in (7, 6) and nxt is not None and not (rel == 0 and modo == "menor")
            and eh_dom7(nxt) and nxt.raiz == (ch.raiz + 5) % 12):
        troot = (ch.raiz - 2) % 12
        off = (troot - t) % 12
        if off in alvos:
            rot = alvos[off][0]
            plano = not nxt.alts and not nxt.sus
            sc = (max(3.3, (diat.score + 0.3) if diat else 0) if final else 2.9) \
                if (ch.meio_dim or diat is None or plano) else 2.6
            it = Interp(sc, "ii_sec", numeral_sec("ii", ch, rot), alvo_pc=troot, alvo_rot=rot)
            it.nota = f"ii–V secundário em direção a {rot} ({nxt.simbolo} é o V7 de {rot})"
            cands.append(it)
        if ch.quinta == 7 and nxt.terca == 4:
            troot2 = (nxt.raiz - 1) % 12
            off2 = (troot2 - t) % 12
            if off2 == 0 or off2 in alvos:
                rot2 = "" if off2 == 0 else alvos[off2][0]
                it = Interp(2.4, "ii_sec", numeral_sec("subii", ch, rot2), alvo_pc=troot2,
                            alvo_rot=rot2 or "I")
                it.nota = f"ii relacionado do subV7 ({nxt.simbolo}): II–subV rumo a {rot2 or 'I'}"
                cands.append(it)

    if (ch.terca == 3 and ch.setima == 10 and ch.quinta in (7, 6) and nxt is not None and not (rel == 0 and modo == "menor")
            and eh_dom7(nxt) and nxt.raiz == (ch.raiz - 1) % 12):
        troot = (ch.raiz - 2) % 12
        off = (troot - t) % 12
        if off in alvos:
            rot = alvos[off][0]
            sc = (max(3.3, (diat.score + 0.3) if diat else 0) if final else 2.9) \
                if (ch.meio_dim or diat is None) else 2.6
            it = Interp(sc, "ii_sec", numeral_sec("ii", ch, rot), alvo_pc=troot, alvo_rot=rot)
            it.nota = f"ii–subV: {ch.simbolo} é o ii de {rot} e {nxt.simbolo} é o subV7 de {rot}"
            cands.append(it)

    if (ch.terca == 3 and ch.setima == 10 and ch.quinta == 7 and diat is None
            and explicado_no_tom(ch, tom) is None and rel != 0):
        troot = (ch.raiz - 2) % 12
        off = (troot - t) % 12
        if off in alvos and not alvos[off][1] and not any(c.tipo == "ii_sec" for c in cands):
            rot = alvos[off][0]
            it = Interp(2.0, "ii_sec", numeral_sec("ii", ch, rot), alvo_pc=troot, alvo_rot=rot)
            it.nota = f"m7 fora do campo: lido como ii de {rot} (ii–V secundário, V7 omitido ou substituído)"
            cands.append(it)

    # ---- 7) napolitano -------------------------------------------------------
    if rel == 1 and ch.terca == 4 and ch.quinta == 7 and ch.setima is None:
        inv, _ = inv_efetiva(ch)
        sc = 2.3 + (0.4 if (rel_nxt in (7, 0) or inv == 1) else 0.0)
        it = Interp(sc, "napolitano", "♭II" + ("6 (N6)" if inv == 1 else " (N)"))
        it.nota = "Acorde napolitano: tríade maior sobre o ♭2, função de pré-dominante"
        cands.append(it)

    # ---- 8) cromático (fallback) ---------------------------------------------
    base_set = SETS["maior" if modo == "maior" else "menor natural"]
    frac = len(core & base_set) / max(1, len(core))
    crom = Interp(-2.5 + 1.5 * frac, "cromatico", rom)
    crom.nota = "Acorde fora do campo e sem encaixe como empréstimo modal: indício de outra tonalidade"
    if rel in (3, 4, 8, 9) and ch.terca in (3, 4) and ch.setima in (None, 10, 11):
        crom.nota += "; relação de mediante cromática com a tônica"
    cands.append(crom)

    cands.sort(key=lambda c: -c.score)
    best = cands[0]
    best.alternativas = [f"{c.grau} ({ROTULO[c.tipo]})" for c in cands[1:]
                         if c.tipo != best.tipo and c.tipo != "cromatico"
                         and c.score >= max(1.8, best.score - 1.2)][:2]
    return best


ROTULO = {
    "diatonico": "diatônico", "emprestimo": "empréstimo modal", "dom_sec": "dominante secundário",
    "sub_dom": "dominante substituto", "ii_sec": "ii–V secundário", "dim_sec": "sensível secundária",
    "dim_pass": "diminuto de passagem", "napolitano": "napolitano", "cromatico": "cromático",
    "dom_est": "dominante estendido", "dom_mod": "dominante de modulação",
}


# =============================================================================
# 6. ESCALA DO ACORDE (chord-scale), FUNÇÃO E DESCRIÇÃO
# =============================================================================
def tem_tensao_menor(ch: Acorde) -> bool:
    return bool(set(ch.alts) & {"b9", "b13", "#5", "b5", "alt", "#9"}) or ch.quinta in (6, 8)


def escala_dominante(ch: Acorde, alvo_menor: bool = False, sub: bool = False) -> str:
    alts = set(ch.alts)
    if ch.sus:
        return "Hexa. IV:Vo" if alvo_menor else "Hexa. IV:Vm"
    if alts & {"#5", "b5", "alt", "#9"} or ch.quinta in (6, 8):
        return "Alt."
    if alts & {"b9", "b13"}:
        return "Mixo. b9 b13"
    if sub or "#11" in alts:
        return "Lydian b7"
    return "Mixo. b9 b13" if alvo_menor else "Mixo."


def escala_acorde_en(it: Interp, ch: Acorde, tom, nxt: Optional[Acorde]) -> str:
    t, modo = tom
    rel = (ch.raiz - t) % 12
    tp = it.tipo
    nxt_menor = nxt is not None and nxt.terca == 3
    if tp in ("dom_sec", "dom_est", "dom_mod"):
        alvo_menor = nxt_menor and it.alvo_pc is not None and nxt.raiz == it.alvo_pc
        return escala_dominante(ch, alvo_menor)
    if tp == "sub_dom":
        return escala_dominante(ch, False, sub=True)
    if tp == "ii_sec":
        if ch.meio_dim:
            return "Locrian n13"
        alvo_min = (it.alvo_rot in ("II", "III", "VI")) if modo == "maior" else (it.alvo_rot == "IV")
        return "Dorian b2" if ((nxt is not None and tem_tensao_menor(nxt)) or alvo_min) else "Dorian"
    if tp == "dim_pass":
        return "Dim."
    if tp == "dim_sec":
        return "Alt.Dom.o7" if ch.dim7 else ("Locrian n13" if ch.meio_dim else "Locrian")
    if tp == "napolitano":
        return "Lydian"
    if tp == "cromatico":
        return ""
    # diatônico ou empréstimo
    if ch.dim7:
        return "Alt.Dom.o7"
    if ch.meio_dim:
        return "Locrian n13" if rel == 2 else "Locrian"
    if eh_dom7(ch):
        if rel == 10:
            return "Lydian b7"
        if rel == 7:
            return escala_dominante(ch, modo == "menor")
    if rel == 10 and ch.terca == 4 and ch.setima is None:
        return "Lydian b7"
    if rel == 10 and ch.terca == 4 and ch.setima == 11:
        return "Ionian"
    if ch.terca == 3 and ch.setima is None and "add6" in ch.adds and rel in (0, 9):
        return "Mel. min"
    if rel == 2 and ch.terca == 3 and nxt is not None and tem_tensao_menor(nxt) and eh_dom7(nxt):
        return "Dorian b2"
    esc = ESCALAS[it.escala]
    return nome_modo(it.escala, esc.index(rel)) if rel in esc else ""


def completar_todos(linhas: list, hints: Dict[int, str]):
    for j, L in enumerate(linhas):
        it, ch, tom = L["interp"], L["acorde"], L["tom"]
        nxt = linhas[j + 1]["acorde"] if j + 1 < len(linhas) else None
        t, modo = tom
        rel = (ch.raiz - t) % 12
        if it.tipo in ("diatonico", "emprestimo"):
            it.funcao = FUNCAO[modo][rel]
            if eh_dom7(ch) and rel == 7:
                it.funcao = "Dominante (V7)"
        elif it.tipo == "dom_sec":
            it.funcao = f"Dominante secundária → {it.alvo_rot}"
        elif it.tipo == "dom_est":
            it.funcao = f"Dominante estendido → {it.alvo_rot}"
        elif it.tipo == "dom_mod":
            it.funcao = f"Dominante do novo tom → {it.alvo_rot}"
        elif it.tipo == "sub_dom":
            it.funcao = f"Dominante substituto → {it.alvo_rot}"
        elif it.tipo == "dim_sec":
            it.funcao = f"Sensível secundária → {it.alvo_rot}"
        elif it.tipo == "dim_pass":
            it.funcao = "Diminuto de passagem (cromatismo)"
        elif it.tipo == "ii_sec":
            it.funcao = f"Subdominante secundária → {it.alvo_rot}"
        elif it.tipo == "napolitano":
            it.funcao = "Subdominante (pré-dominante)"
        else:
            it.funcao = "—"
        en = escala_acorde_en(it, ch, tom, nxt)
        it.esc_acorde = fmt_escala(ch.nome_raiz, en)
        if en == "Aeolian" and modo == "menor" and rel == 0:
            it.esc_acorde += "  |  alternativa: " + fmt_escala(ch.nome_raiz, "Dorian")


# =============================================================================
# 7. DETECÇÃO DE TONALIDADE (VITERBI) E MODULAÇÕES
# =============================================================================
CHAVES: List[Tuple[int, str]] = [(t, m) for t in range(12) for m in ("maior", "menor")]


# -----------------------------------------------------------------------------
# Evidência harmônica contextual para a escolha do centro tonal.
# -----------------------------------------------------------------------------
# A versão anterior fazia Viterbi usando apenas a pontuação de cada acorde em
# cada tom. Isso é insuficiente em progressões como ii–V–I: o ii e o V podem
# parecer "secundários" isoladamente, embora o conjunto seja justamente a
# evidência mais forte de que o novo centro começou ali.


def _acorde_estavel_como_tonica(ch: Acorde) -> bool:
    """Acorde com perfil plausível de I/i (maj7, m7 etc.).

    Dominantes 7 não são considerados tônicas aqui. Caso contrário, uma cadeia
    como D7→G7 poderia ser erroneamente convertida em "tom de Sol". O caso de
    blues já é tratado separadamente por detectar_blues().
    """
    if eh_dom7(ch):
        return False
    if ch.quinta not in (7, None):
        return False
    if ch.terca in (3, 4):
        return True
    return ch.terca is None and ch.setima in (None, 11)


def _modo_tonica_do_acorde(ch: Acorde) -> Optional[str]:
    if ch.terca == 3:
        return "menor"
    if ch.terca == 4:
        return "maior"
    if ch.terca is None:
        return None
    return None


def _alvo_ii_v_i_detour(acordes: List[Acorde], i: int) -> Optional[Tuple[int, str]]:
    """Detecta um ii–V–I que parece tonicização, pois o acorde-alvo é o ii
    de uma tonalidade maior que imediatamente recebe V→I.

    Ex.: Gm7–C7–Fm7–Bb7–Ebmaj7. O Gm7–C7 pode sugerir F menor, mas o Fm7
    funciona como ii de Eb e Bb7→Ebmaj7 confirma o centro anterior.
    """
    alvo = _alvo_ii_v_i(acordes, i)
    if alvo is None or alvo[1] != "menor" or i + 3 >= len(acordes):
        return None
    target_chord = acordes[i + 2]
    major_center = _alvo_v_i(acordes, i + 3)
    if major_center is None or major_center[1] != "maior":
        return None
    if (target_chord.raiz - major_center[0]) % 12 != 2:
        return None
    return alvo


def _alvo_ii_v_i(acordes: List[Acorde], i: int) -> Optional[Tuple[int, str]]:
    """Retorna o centro-alvo de um ii–V–I que começa em i."""
    if i + 2 >= len(acordes):
        return None
    a, b, c = acordes[i], acordes[i + 1], acordes[i + 2]
    if not (a.menor7 or a.meio_dim):
        return None
    if not eh_dom7(b):
        return None
    if b.raiz != (a.raiz + 5) % 12 or c.raiz != (b.raiz + 5) % 12:
        return None
    if not _acorde_estavel_como_tonica(c):
        return None
    modo = _modo_tonica_do_acorde(c)
    if modo is None:
        return None
    return c.raiz, modo


def _alvo_v_i(acordes: List[Acorde], i: int) -> Optional[Tuple[int, str]]:
    """Retorna o centro-alvo de uma resolução V→I em i,i+1."""
    if i + 1 >= len(acordes):
        return None
    a, b = acordes[i], acordes[i + 1]
    if not eh_dom7(a) or a.raiz != (b.raiz + 7) % 12:
        return None
    if not _acorde_estavel_como_tonica(b):
        return None
    modo = _modo_tonica_do_acorde(b)
    if modo is None:
        return None
    return b.raiz, modo


def _alvo_v_de_vi_para_centro(acordes: List[Acorde], i: int) -> Optional[Tuple[int, str]]:
    """Detecta o padrão V/vi → vi → ii–V–I do centro maior.

    Esse caso é importante em All the Things You Are: C7alt → Fm7 não cria
    Fm como novo centro; o C7 está em Ab como V de vi e o Fm7 é seguido por
    Bbm7–Eb7–Abmaj7. A sequência completa resolve a interpretação em Ab.
    """
    if i + 4 >= len(acordes):
        return None
    dom, vi = acordes[i], acordes[i + 1]
    if not eh_dom7(dom) or vi.terca != 3 or dom.raiz != (vi.raiz + 7) % 12:
        return None
    alvo = _alvo_ii_v_i(acordes, i + 2)
    if alvo is None or alvo[1] != "maior":
        return None
    centro, modo = alvo
    # vi da tonalidade candidata: 9 semitons acima da tônica.
    if (vi.raiz - centro) % 12 != 9:
        return None
    return centro, modo


def _alvo_ii_v_janela(acordes: List[Acorde], i: int, max_gap: int = 3) -> Optional[Tuple[int, str]]:
    """Detecta ii ... V com pequenos acordes de desvio entre os dois.

    Exemplo do Tune Up: Emin7–F7–Bbmaj7–A7. O Emin7 é o ii e o A7 é o V
    de D, embora exista uma "detour cadence" entre eles. O centro-alvo é D
    desde o início desse trecho.
    """
    if i >= len(acordes):
        return None
    a = acordes[i]
    if not (a.menor7 or a.meio_dim):
        return None
    alvo = (a.raiz - 2) % 12
    v_esperado = (alvo + 7) % 12
    for j in range(i + 1, min(len(acordes), i + max_gap + 1)):
        ch = acordes[j]
        if not eh_dom7(ch) or ch.raiz != v_esperado:
            continue
        # Se o V for seguido pelo próprio alvo, temos um ii–V–I comum;
        # nesses casos o detector mais específico já cuida da prioridade.
        if j + 1 < len(acordes) and acordes[j + 1].raiz == alvo:
            return None
        # Se, em vez de resolver em `alvo`, o V for seguido por outro ii–V–I
        # claramente direcionado a uma tonalidade diferente, estamos diante de
        # um desvio/tonicização, não de um novo centro. Ex.: Cmin7–F7–Fmin7–
        # Bb7–Ebmaj7; F7 é V/Bb, mas a frase retorna a Eb.
        if j + 3 < len(acordes):
            proximo_alvo = _alvo_ii_v_i(acordes, j + 1)
            if proximo_alvo is not None and proximo_alvo != (alvo, "menor" if a.meio_dim else "maior"):
                return None
        modo = "menor" if a.meio_dim else "maior"
        return alvo, modo
    return None


def _alvo_ii_v_aberto(acordes: List[Acorde], i: int) -> Optional[Tuple[int, str]]:
    """Centro-alvo de ii–V sem acorde I explícito.

    É usado principalmente no fim da progressão, onde a fonte pode rotular o
    trecho como "ii–V do tônico" mesmo sem mostrar a resolução. Para evitar
    falsos centros no meio da música, a evidência é liberada só quando o V é o
    último acorde ou não é seguido pelo próprio alvo.
    """
    if i + 1 >= len(acordes):
        return None
    a, b = acordes[i], acordes[i + 1]
    if not (a.menor7 or a.meio_dim) or not eh_dom7(b):
        return None
    if b.raiz != (a.raiz + 5) % 12:
        return None
    alvo = (b.raiz + 5) % 12
    modo = "menor" if a.meio_dim else "maior"
    if i + 2 < len(acordes) and acordes[i + 2].raiz == alvo:
        return None
    return alvo, modo


def _alvo_ii_subv_i(acordes: List[Acorde], i: int) -> Optional[Tuple[int, str]]:
    """Retorna o centro-alvo de ii–subV–I, quando a sequência estiver explícita."""
    if i + 2 >= len(acordes):
        return None
    a, b, c = acordes[i], acordes[i + 1], acordes[i + 2]
    if not (a.menor7 or a.meio_dim):
        return None
    if not (b.terca == 4 and b.setima == 10):
        return None
    # subV7 resolve meio-tom abaixo.
    if c.raiz != (b.raiz - 1) % 12 or not _acorde_estavel_como_tonica(c):
        return None
    modo = _modo_tonica_do_acorde(c)
    return (c.raiz, modo) if modo else None


def _alvos_contextuais(acordes: List[Acorde], i: int) -> Dict[Tuple[int, str], float]:
    """Mapeia centros-alvo que recebem evidência estrutural na posição i."""
    out: Dict[Tuple[int, str], float] = {}
    alvo = _alvo_ii_v_i(acordes, i)
    if alvo:
        out[alvo] = max(out.get(alvo, 0.0), 4.8)
        # A segunda e a terceira posições ainda pertencem à mesma cadência.
        for k, bonus in ((i + 1, 3.9), (i + 2, 3.3)):
            # O consumidor desta função usa a posição do alvo; os pesos destas
            # posições são tratados abaixo por _bonus_contextual_tonal.
            pass
    alvo = _alvo_ii_subv_i(acordes, i)
    if alvo:
        out[alvo] = max(out.get(alvo, 0.0), 4.4)
    alvo = _alvo_v_i(acordes, i)
    if alvo:
        out[alvo] = max(out.get(alvo, 0.0), 2.2)
    alvo = _alvo_ii_v_aberto(acordes, i)
    if alvo:
        out[alvo] = max(out.get(alvo, 0.0), 3.5)
    return out


def _seguido_por_cadencia_distinta(acordes: List[Acorde], i: int, alvo: Tuple[int, str]) -> bool:
    """Indica se o acorde-alvo de um V→I é imediatamente reinterpretado como
    preparação de outro centro por um ii–V–I completo.

    Ex.: C7→Fm7→Bbm7→Eb7→Abmaj7. O Fm7 é vi de Ab, portanto o V→Fm7 não
    deve criar automaticamente um "tom de F menor".
    """
    if i + 3 >= len(acordes):
        return False
    prox = _alvo_ii_v_i(acordes, i + 1)
    return prox is not None and prox != alvo


def _bonus_contextual_tonal(acordes: List[Acorde], i: int, tom) -> float:
    """Bônus de padrões harmônicos que apontam explicitamente para `tom`."""
    b = 0.0
    # ii–V–I: quando estamos no ii, já sabemos qual é o centro-alvo.
    for k, peso in ((i, 4.8), (i - 1, 3.9), (i - 2, 3.3)):
        if k < 0:
            continue
        if k + 2 < len(acordes):
            alvo_ii = _alvo_ii_v_i(acordes, k)
            if alvo_ii == tom and _alvo_ii_v_i_detour(acordes, k) != tom:
                b = max(b, peso)
            if _alvo_ii_subv_i(acordes, k) == tom:
                b = max(b, peso - 0.4)
        # ii–V aberto só precisa de dois acordes e é especialmente útil no
        # fechamento de uma fonte que nomeia explicitamente o "ii-V do tônico".
        if k + 1 < len(acordes) and _alvo_ii_v_aberto(acordes, k) == tom:
            b = max(b, 3.1 if peso >= 3.9 else 2.8)
        if _alvo_ii_v_janela(acordes, k) == tom:
            b = max(b, 4.2 if peso >= 3.9 else 3.5)
        if _alvo_v_de_vi_para_centro(acordes, k) == tom:
            b = max(b, 5.0 if peso >= 3.9 else 4.0)
    # V→I: evidência menor que ii–V–I, porque uma resolução isolada pode ser
    # apenas uma tonicização dentro do tom anterior (ex.: V/vi).
    for k, peso in ((i, 2.2), (i - 1, 1.8)):
        if k < 0 or k + 1 >= len(acordes):
            continue
        alvo_v = _alvo_v_i(acordes, k)
        if alvo_v == tom:
            if _seguido_por_cadencia_distinta(acordes, k, alvo_v):
                continue
            b = max(b, peso)
    return b


def _evidencia_tonica(acordes: List[Acorde], i: int, tom, interp: Interp) -> float:
    """Evidência adicional de um centro tonal local, sem reclassificar o acorde."""
    t, modo = tom
    ch = acordes[i]
    rel = (ch.raiz - t) % 12
    b = 0.0

    # A própria tônica recebe um reforço contextual. Isso evita que um único
    # acorde perfeitamente diatônico do tom anterior domine uma nova cadência.
    if rel == 0 and _acorde_estavel_como_tonica(ch):
        b += 1.25
        if ch.setima == 11 and i + 1 < len(acordes):
            b += 0.25
        if i > 0 and eh_dom7(acordes[i - 1]) and acordes[i - 1].raiz == (ch.raiz + 7) % 12:
            # Se este I é imediatamente sucedido por outro ii–V–I, a leitura
            # como tônica isolada tende a ser uma tonicização (ex.: vi de Ab).
            alvo_v = _alvo_v_i(acordes, i - 1)
            b += 0.35 if _seguido_por_cadencia_distinta(acordes, i - 1, alvo_v) else 1.15

    # Um ii ou V que prepara a tônica candidata é evidência muito forte de um
    # centro que começa antes do acorde I, que é exatamente o comportamento
    # observado nos exemplos dos PDFs.
    b += _bonus_contextual_tonal(acordes, i, tom)

    # Caso especial/generalizado de V/vi → vi seguido de um ii–V–I que confirma
    # a tonalidade maior. Mantém o centro no maior (em vez de criar um modo
    # menor artificial sobre o acorde vi).
    for k, peso in ((i, 5.0), (i - 1, 4.0)):
        if k >= 0 and _alvo_v_de_vi_para_centro(acordes, k) == tom:
            b = max(b, peso)

    # Antecipação de um ii–V–I que começa no próximo acorde. Isso é essencial
    # quando o primeiro acorde do novo trecho é o vi/iii de uma tonalidade
    # maior (ex.: Fm7 | Bbm7 | Eb7 | Abmaj7): o centro é Ab desde o Fm7,
    # embora o acorde inicial isolado possa parecer uma tônica menor.
    for k, peso in ((i + 1, 2.6), (i + 2, 2.8), (i + 3, 1.0)):
        if k < 0 or k + 2 >= len(acordes):
            continue
        alvo = _alvo_ii_v_i(acordes, k)
        if alvo == tom:
            b = max(b, peso)
        alvo = _alvo_ii_subv_i(acordes, k)
        if alvo == tom:
            b = max(b, peso - 0.3)

    # Sequências locais coerentes merecem uma pequena vantagem. A ideia não é
    # contar novamente toda a análise, mas evitar que um cromatismo isolado
    # faça o Viterbi trocar de estado.
    viz = 0
    for j in (i - 1, i + 1):
        if 0 <= j < len(acordes):
            it = interpretar(acordes[j], tom, j, acordes, final=False)
            if it.tipo in ("diatonico", "emprestimo"):
                viz += 0.25
    b += viz

    # A leitura cromática pura deve ser fortemente desfavorecida como centro
    # quando o acorde pode ser explicado por um ii–V ou V–I em outro tom.
    if interp.tipo == "cromatico":
        b -= 0.8
    return b


def _forca_segmento_local(acordes: List[Acorde], ini: int, fim: int, tom, matriz) -> float:
    """Mede quão coerente é um trecho inteiro com um centro."""
    if fim < ini:
        return -1e9
    pontos = []
    for i in range(ini, fim + 1):
        it = matriz[i][CHAVES.index(tom)]
        pontos.append(it.score + _evidencia_tonica(acordes, i, tom, it))
    if not pontos:
        return -1e9
    media = sum(pontos) / len(pontos)
    # Penaliza levemente trechos muito curtos sem qualquer chegada harmônica,
    # mas não penaliza uma tônica curtíssima quando ela é o alvo de ii–V–I.
    chegada = any(_bonus_contextual_tonal(acordes, i, tom) >= 3.0 for i in range(ini, fim + 1))
    if len(pontos) == 1 and not chegada:
        media -= 0.6
    return media


def _evidencia_mudanca(a, b, acordes: List[Acorde], i: int) -> float:
    """Força da evidência de que b começa na posição i."""
    if a == b:
        return 0.0
    target = _bonus_contextual_tonal(acordes, i, b)
    return max(target, _bonus_contextual_tonal(acordes, max(0, i - 1), b) * 0.85)


def _penalidade_mod_contextual(a, b, acordes: List[Acorde], i: int) -> float:
    """Penalidade adaptativa: muda-se de tom com menos resistência quando há ii–V–I."""
    base = penalidade_mod(a, b)
    evid = _evidencia_mudanca(a, b, acordes, i)
    if evid >= 4.0:
        return base * 0.18
    if evid >= 3.0:
        return base * 0.38
    if evid >= 2.0:
        return base * 0.65
    return base


def _pos_quintas(tom) -> int:
    t, m = tom
    # O menor relativo é deslocado para a posição do seu relativo maior.
    maior_rel = t if m == "maior" else (t + 3) % 12
    return (maior_rel * 7) % 12


def _dist_quintas(a, b) -> int:
    d = (_pos_quintas(b) - _pos_quintas(a)) % 12
    return d - 12 if d > 6 else d


def _dist_quintas_local(a, b) -> int:
    return abs(_dist_quintas(a, b))


def penalidade_mod(a, b) -> float:
    """Custo base da mudança tonal.

    A penalidade deixou de ser artificialmente baixa para toda relação de uma
    quinta e passa a refletir o fato de que uma mudança deve ser justificada
    por evidência harmônica local. A função é mantida separada porque outras
    partes do programa usam o conceito de distância entre tons.
    """
    if a == b:
        return 0.0
    d = _dist_quintas_local(a, b)
    if d == 1:
        return 2.6
    if d == 2:
        return 3.3
    if d == 3:
        return 4.0
    return 4.4 + 0.35 * (d - 3)


def _evidencia_dura_mudanca(acordes: List[Acorde], i: int, tom) -> float:
    """Evidência explícita suficiente para sustentar uma nova tonalidade em i."""
    best = 0.0
    # Padrões que começam em i ou nos 2 acordes anteriores.
    for k in range(max(0, i - 2), i + 1):
        if k + 2 < len(acordes) and _alvo_ii_v_i(acordes, k) == tom:
            if _alvo_ii_v_i_detour(acordes, k) != tom:
                best = max(best, 4.8 if k == i else 3.9 if k == i - 1 else 3.3)
        if k + 2 < len(acordes) and _alvo_ii_subv_i(acordes, k) == tom:
            best = max(best, 4.4 if k == i else 3.5)
        if k + 1 < len(acordes) and _alvo_v_i(acordes, k) == tom:
            # V→I é evidência de modulação quando o V realmente aponta ao novo
            # centro; ainda é deliberadamente mais fraca que um ii–V–I.
            best = max(best, 3.0 if k == i else 2.5)
        if k + 1 < len(acordes) and _alvo_ii_v_aberto(acordes, k) == tom:
            best = max(best, 3.4 if k == i else 3.0)
        if _alvo_ii_v_janela(acordes, k) == tom:
            best = max(best, 4.2 if k == i else 3.6)
        if _alvo_v_de_vi_para_centro(acordes, k) == tom:
            best = max(best, 5.0 if k == i else 4.2)

    # Antecipação: o novo centro pode ser introduzido pelo acorde que vem antes
    # do ii (caso de vi → ii–V–I / retorno à tonalidade maior).
    for k, peso in ((i + 1, 2.6), (i + 2, 2.8), (i + 3, 1.0)):
        if k + 2 < len(acordes) and _alvo_ii_v_i(acordes, k) == tom:
            best = max(best, peso)
        if k + 2 < len(acordes) and _alvo_ii_subv_i(acordes, k) == tom:
            best = max(best, peso - 0.3)
    return best


def _refinar_caminho_tonal(acordes: List[Acorde], caminho: List[Tuple[int, str]], matriz) -> List[Tuple[int, str]]:
    """Remove trocas sem evidência e preserva tônicas reais nas chegadas.

    O Viterbi continua sendo o mecanismo principal, mas uma troca causada por
    um único acorde cromático não deve sobreviver ao pós-processamento se não
    houver ii–V/V–I/tonicização explícita. Por outro lado, uma nova tônica
    forte deve poder encerrar uma excursão curta, como o Ebmaj7 após o ii–V não
    resolvido de G menor em There Will Never Be Another You.
    """
    n = len(caminho)
    if n == 0:
        return caminho

    # Âncora inicial: uma cifra maj7/minmaj7 explícita no primeiro acorde é uma
    # evidência muito forte do centro inicial e evita ler um I como III/vi de
    # um relativo apenas porque uma cadência aparece logo depois.
    primeiro = acordes[0]
    if primeiro.terca == 4 and primeiro.setima == 11:
        caminho[0] = (primeiro.raiz, "maior")
    elif primeiro.terca == 3 and primeiro.setima == 11:
        caminho[0] = (primeiro.raiz, "menor")

    for i in range(1, n):
        anterior, atual = caminho[i - 1], caminho[i]
        if atual == anterior:
            continue
        evid = _evidencia_dura_mudanca(acordes, i, atual)
        ch = acordes[i]
        it_atual = matriz[i][CHAVES.index(atual)]
        it_ant = matriz[i][CHAVES.index(anterior)]

        # Uma tônica forte permite encerrar uma excursão, mas, quando esse
        # centro já apareceu e o acorde está imediatamente antes de outra
        # cadência para um terceiro centro, ele pode ser apenas um acorde de
        # passagem (caso de Abmaj7 antes de Am7–D7–Gmaj7).
        proximo_alvo = None
        for kk in (i + 1, i + 2):
            if kk + 2 < n:
                cand = (_alvo_ii_v_i(acordes, kk) or _alvo_ii_subv_i(acordes, kk))
                if cand is not None:
                    if _alvo_ii_v_i_detour(acordes, kk) != cand:
                        proximo_alvo = cand
                        break
        centro_ja_visto = atual in caminho[:i]
        tonic_forte = (
            _acorde_estavel_como_tonica(ch)
            and ch.raiz == atual[0]
            and _modo_tonica_do_acorde(ch) == atual[1]
            and not (centro_ja_visto and proximo_alvo not in (None, atual))
        )

        # Sem evidência estrutural nem chegada em uma tônica forte, a troca é
        # quase certamente uma reinterpretação/acorde cromático transitório.
        if evid < 2.8 and not tonic_forte:
            caminho[i] = anterior

    # Reentrada em um centro maior já estabelecido: uma cifra maj7 no grau I
    # de um centro que apareceu anteriormente é uma confirmação muito forte de
    # retorno. Isso resolve, por exemplo, o Ebmaj7 que encerra o ii–V não
    # resolvido de G menor em There Will Never Be Another You.
    centros_vistos = set(caminho[:1])
    for i in range(1, n):
        atual = caminho[i]
        ch = acordes[i]
        candidato = (ch.raiz, "maior") if ch.terca == 4 and ch.setima == 11 else None
        if candidato and candidato != atual and candidato in centros_vistos:
            # Não force a volta se a tônica está imediatamente funcionando como
            # acorde de passagem antes de um novo ii–V–I para outro centro.
            proximo_alvo = None
            for kk in (i + 1, i + 2):
                if kk + 2 < n:
                    cand = (_alvo_ii_v_i(acordes, kk)
                            or _alvo_ii_subv_i(acordes, kk))
                    if cand is not None and _alvo_ii_v_i_detour(acordes, kk) != cand:
                        proximo_alvo = cand
                        break
            if proximo_alvo in (None, candidato):
                caminho[i] = candidato
                atual = candidato
        centros_vistos.add(atual)

    # Depois de eliminar trocas espúrias, propaga a decisão para frente dentro
    # da mesma sequência quando o estado anterior foi revertido.
    for i in range(1, n):
        if caminho[i] != caminho[i - 1]:
            # Mantém explicitamente uma mudança sustentada por evidência.
            if _evidencia_dura_mudanca(acordes, i, caminho[i]) >= 2.8:
                continue
            ch = acordes[i]
            if (_acorde_estavel_como_tonica(ch) and ch.raiz == caminho[i][0]
                    and _modo_tonica_do_acorde(ch) == caminho[i][1]):
                continue
            caminho[i] = caminho[i - 1]
    return caminho


def decodificar_tons(acordes: List[Acorde]):
    """Escolhe a sequência de tonalidades usando evidência de curto alcance.

    Diferenças principais em relação ao Viterbi original:
      * ii–V–I e V–I dão bônus ao TOM-ALVO, inclusive no acorde ii;
      * a penalidade de troca é adaptativa e quase desaparece diante de uma
        cadência explícita;
      * a decisão usa os acordes vizinhos para impedir que um único acorde
        diatônico do tom anterior "segure" a tonalidade errada;
      * a grafia do centro é resolvida depois pela frequência das cifras.
    """
    n, K = len(acordes), len(CHAVES)
    matriz = [[interpretar(ch, k, i, acordes) for k in CHAVES] for i, ch in enumerate(acordes)]
    NEG = -1e18
    dp = [[NEG] * K for _ in range(n)]
    bp = [[0] * K for _ in range(n)]

    for k, tom in enumerate(CHAVES):
        it = matriz[0][k]
        dp[0][k] = it.score + _evidencia_tonica(acordes, 0, tom, it) + (0.02 if tom[1] == "maior" else 0.0)

    for i in range(1, n):
        for k, tom in enumerate(CHAVES):
            it = matriz[i][k]
            local = it.score + _evidencia_tonica(acordes, i, tom, it)
            melhor, arg = NEG, 0
            for kp, tom_prev in enumerate(CHAVES):
                v = dp[i - 1][kp]
                if tom_prev != tom:
                    v -= _penalidade_mod_contextual(tom_prev, tom, acordes, i)
                # Uma troca sem qualquer evidência concreta é desestimulada
                # adicionalmente; isso elimina falsas modulações cromáticas.
                if tom_prev != tom and _evidencia_mudanca(tom_prev, tom, acordes, i) < 1.5:
                    v -= 0.9
                if v > melhor:
                    melhor, arg = v, kp
            dp[i][k] = melhor + local
            bp[i][k] = arg

    # Reconstrução com uma pequena preferência por maior em empate praticamente
    # exato, mas sem a antiga preferência fixa pelo modo maior.
    k = max(range(K), key=lambda x: (dp[n - 1][x], CHAVES[x][1] == "maior"))
    caminho = [k]
    for i in range(n - 1, 0, -1):
        k = bp[i][k]
        caminho.append(k)
    caminho.reverse()
    caminho_tons = [CHAVES[k] for k in caminho]
    caminho_tons = _refinar_caminho_tonal(acordes, caminho_tons, matriz)
    return caminho_tons, matriz


def detectar_blues(acordes: List[Acorde]) -> Optional[int]:
    """Blues: só dominantes (7ª) sobre I, IV e V. Retorna a tônica ou None."""
    if len(acordes) < 3 or not all(a.terca == 4 and a.setima == 10 for a in acordes):
        return None
    for t in (acordes[0].raiz, acordes[-1].raiz):
        rels = {(a.raiz - t) % 12 for a in acordes}
        if rels <= {0, 5, 7} and 0 in rels and len(rels) >= 2:
            return t
    return None


def interp_blues(ch: Acorde, t: int) -> Interp:
    rel = (ch.raiz - t) % 12
    base = {0: "I", 5: "IV", 7: "V"}[rel]
    it = Interp(3.0, "diatonico", numeral(base, ch, ch.inversao()), escala="mixolídio")
    it.funcao = {0: "Tônica", 5: "Subdominante", 7: "Dominante"}[rel]
    it.esc_acorde = fmt_escala(ch.nome_raiz, "Mixo.") + " / escala de blues"
    return it


def descrever_modulacao(a, b, hints) -> str:
    rel = (b[0] - a[0]) % 12
    grau = base_romana(rel, a[1])
    grau = grau.lower() if b[1] == "menor" else grau.upper()
    d = _dist_quintas(a, b)
    if a[0] == b[0]:
        tipo = "mudança de modo (tom homônimo/paralelo)"
    elif d == 0:
        tipo = "modulação para o tom relativo"
    elif d == 1:
        tipo = "modulação para a região da dominante"
    elif d == -1:
        tipo = "modulação para a região da subdominante"
    elif abs(d) == 2:
        tipo = "modulação para tom vizinho (2 passos no ciclo das quintas)"
    else:
        tipo = f"modulação para tom distante ({abs(d)} passos no ciclo das quintas)"
    extra = "" if a[0] == b[0] else f"; o novo tom corresponde ao grau {grau} de {cifra_tom(a, hints)}"
    return f"{nome_tom(a, hints)} → {nome_tom(b, hints)}: {tipo}{extra}"


# =============================================================================
# 8. CAMPOS HARMÔNICOS
# =============================================================================
TRIADES = {(4, 7): "", (3, 7): "m", (3, 6): "dim", (4, 8): "aug"}
TETRADES = {(4, 7, 11): "maj7", (4, 7, 10): "7", (3, 7, 10): "m7", (3, 6, 10): "m7(b5)",
            (3, 6, 9): "dim7", (3, 7, 11): "m(maj7)", (4, 8, 11): "maj7(#5)", (4, 8, 10): "7(#5)"}


def campo_harmonico(tonica: str, escala: str):
    """Empilha terças sobre cada grau. Retorna lista (romano, tríade, tétrade)."""
    iv = ESCALAS[escala]
    notas = soletrar_escala(tonica, iv)
    linhas = []
    for i in range(7):
        r = notas[i]
        t3 = (iv[(i + 2) % 7] - iv[i]) % 12
        t5 = (iv[(i + 4) % 7] - iv[i]) % 12
        t7 = (iv[(i + 6) % 7] - iv[i]) % 12
        q3 = TRIADES.get((t3, t5), "?")
        q4 = TETRADES.get((t3, t5, t7), "?")
        try:
            rom3 = numeral(ROMANOS[i], parse_acorde(r + q3), 0)
            rom4 = numeral(ROMANOS[i], parse_acorde(r + q4), 0)
        except ValueError:
            rom3 = rom4 = ROMANOS[i]
        linhas.append((rom3, r + q3, rom4, r + q4))
    return notas, linhas


CAMPOS_DO_MODO = {"maior": ["maior", "maior harmônico"],
                  "menor": ["menor natural", "menor harmônica", "menor melódica"]}


# =============================================================================
# 9. ANÁLISE COMPLETA
# =============================================================================
def analisar(texto: str) -> dict:
    simbolos = separar_progressao(texto)
    if not simbolos:
        raise ValueError("Digite pelo menos um acorde.")
    acordes, erros = [], []
    for s in simbolos:
        try:
            acordes.append(parse_acorde(s))
        except ValueError as e:
            erros.append(str(e))
    if erros:
        raise ValueError("\n".join(erros))

    # A grafia enarmônica não deve depender do primeiro acorde encontrado.
    # Ex.: em Have You Met Miss Jones, F#dim7 aparece antes de Gbmaj7;
    # para o centro tonal, a grafia local correta é Gb, não F#.
    # Escolhemos a grafia mais frequente para cada classe de altura.
    grafias: Dict[int, Dict[str, int]] = {}
    for ch in acordes:
        grafias.setdefault(ch.raiz, {})[ch.nome_raiz] = grafias.setdefault(ch.raiz, {}).get(ch.nome_raiz, 0) + 1
    hints: Dict[int, str] = {}
    for pc, contagens in grafias.items():
        hints[pc] = max(contagens, key=lambda nome: (contagens[nome], -len(nome)))

    tons, matriz = decodificar_tons(acordes)
    idx = {k: i for i, k in enumerate(CHAVES)}
    blues = detectar_blues(acordes)
    if blues is not None:
        tons = [(blues, "maior")] * len(acordes)
    linhas = []
    for i, ch in enumerate(acordes):
        if blues is not None:
            it = interp_blues(ch, blues)
        else:
            it = interpretar(ch, tons[i], i, acordes, final=True)
        linhas.append({"i": i, "acorde": ch, "tom": tons[i], "interp": it, "notas": []})

    if blues is None:
        completar_todos(linhas, hints)

    # --- segmentos (trechos em um mesmo tom) -----------------------------------
    segmentos = []
    ini = 0
    for i in range(1, len(acordes) + 1):
        if i == len(acordes) or tons[i] != tons[ini]:
            segmentos.append({"ini": ini, "fim": i - 1, "tom": tons[ini]})
            ini = i

    # --- modulações e acorde pivô ----------------------------------------------
    modulacoes = []
    for s_ant, s_nov in zip(segmentos, segmentos[1:]):
        a, b = s_ant["tom"], s_nov["tom"]
        texto_mod = descrever_modulacao(a, b, hints)
        pivo = None
        for j in range(s_nov["ini"] - 1, max(s_ant["ini"] - 1, s_nov["ini"] - 3), -1):
            ia = matriz[j][idx[a]]
            ib = matriz[j][idx[b]]
            if ia.tipo == "diatonico" and ib.tipo == "diatonico":
                pivo = j
                linhas[j]["notas"].append(
                    f"ACORDE PIVÔ: {ia.grau} em {cifra_tom(a, hints)} = "
                    f"{ib.grau} em {cifra_tom(b, hints)}")
                break
        if pivo is not None:
            texto_mod += f". Via acorde pivô ({acordes[pivo].simbolo})"
        else:
            texto_mod += ". Modulação direta (sem acorde pivô diatônico)"
        modulacoes.append({"em": s_nov["ini"], "texto": texto_mod, "pivo": pivo})

    res_acordes = acordes
    # --- anotações: ii–V, cadências, notas e leituras alternativas -----------
    for j, L in enumerate(linhas):
        it, ch = L["interp"], L["acorde"]
        if it.nota:
            L["notas"].insert(0, it.nota)
        if it.alternativas:
            L["notas"].append("Leitura alternativa: " + "; ".join(it.alternativas))
        if it.tipo in ("dom_sec", "sub_dom") and j > 0 and it.alvo_pc is not None:
            ant = linhas[j - 1]
            ca = ant["acorde"]
            if (ant["tom"] == L["tom"] and ant["interp"].tipo != "ii_sec"
                    and ca.terca == 3 and ca.setima == 10
                    and ca.raiz == (it.alvo_pc + 2) % 12):
                ant["notas"] = [x for x in ant["notas"]
                                if not (x.startswith("Leitura alternativa") and "ii–V secundário" in x)]
                ant["notas"].append(f"Funciona como ii{'ø' if ca.quinta == 6 else ''}7/"
                                    f"{it.alvo_rot} (ii–V secundário com {ch.simbolo})")
        if blues is not None:
            if j == 0:
                L["notas"].append("Blues: dominantes (7ª) sobre I, IV e V; não há resolução tonal "
                                  "convencional, cada acorde é soado como 'tônica' do próprio campo mixolídio")
            continue
        cad_dom, dest_c = cadeia_dominantes(res_acordes, j)
        if len(cad_dom) >= 2 and (j == 0 or not (
                res_acordes[j - 1].terca == 4 and res_acordes[j - 1].setima == 10
                and res_acordes[j].raiz == (res_acordes[j - 1].raiz + 5) % 12)):
            seq = " → ".join(res_acordes[k].simbolo for k in cad_dom)
            if dest_c is not None:
                seq += " → " + res_acordes[dest_c].simbolo
            for k in cad_dom:
                linhas[k]["notas"].append(f"Cadeia de dominantes (dominante estendido): {seq}")
        if j + 1 < len(linhas):
            B = linhas[j + 1]
            if B["tom"] == L["tom"]:
                cad = detectar_cadencia(ch, B["acorde"], it, L["tom"])
                if cad and B["interp"].tipo in ("diatonico", "emprestimo"):
                    B["notas"].append(cad)
        elif it.tipo == "diatonico":
            t, modo = L["tom"]
            if (ch.raiz - t) % 12 == 7 and ch.terca in (4, 3) and len(linhas) > 1:
                L["notas"].append("Meia cadência: a progressão termina na dominante")

    # --- escala de cada trecho --------------------------------------------------
    for s in segmentos:
        trecho = linhas[s["ini"]: s["fim"] + 1]
        s["escala"] = resumo_escala(s["tom"], trecho, hints)
        if blues is not None:
            mj = soletrar_escala(nome_tonica(s["tom"], hints), ESCALAS["maior"])
            bem = lambda x: x[:-1] if x.endswith("#") else x + "b"
            bl = [mj[0], bem(mj[2]), mj[3], bem(mj[4]), mj[4], bem(mj[6])]
            s["escala"]["blues"] = "Blues detectado. Escala de blues: " + " ".join(bl)

    return {"texto": texto, "acordes": acordes, "linhas": linhas, "segmentos": segmentos,
            "modulacoes": modulacoes, "hints": hints}


def detectar_cadencia(a: Acorde, b: Acorde, ita: Interp, tom) -> str:
    t, modo = tom
    ra, rb = (a.raiz - t) % 12, (b.raiz - t) % 12
    if ita.tipo not in ("diatonico", "emprestimo", "sub_dom"):
        return ""
    if rb == 0 and b.quinta in (7, None) and (b.terca in (4, None) if modo == "maior" else b.terca in (3, None, 4)):
        if ita.tipo == "sub_dom":
            return "Cadência com dominante substituto (subV7→I)"
        if ra == 7 and a.terca == 4:
            return f"Cadência autêntica ({'V7' if a.setima == 10 else 'V'}→{'I' if modo == 'maior' else 'i'})"
        if ra == 11 and (a.dim_triade or a.dim7 or a.meio_dim):
            return "Cadência autêntica com sensível (vii°→I)"
        if ra == 5:
            return "Cadência plagal (IV→I)" if a.terca != 3 else "Cadência plagal menor (iv→I, empréstimo modal)"
        if ra == 10:
            return "Cadência modal (♭VII→I)" if modo == "maior" else "Cadência subtônica (VII→i)"
    if ra == 7 and a.terca == 4 and ((modo == "maior" and rb == 9) or (modo == "menor" and rb == 8)):
        return "Cadência deceptiva/interrompida (V→" + ("vi)" if modo == "maior" else "VI)")
    return ""


def resumo_escala(tom, trecho, hints) -> dict:
    t, modo = tom
    base = "maior" if modo == "maior" else "menor natural"
    P, fontes = set(), []
    for L in trecho:
        it, ch = L["interp"], L["acorde"]
        if it.tipo in ("diatonico", "emprestimo", "napolitano"):
            P |= {((ch.raiz - t) + x) % 12 for x in ch.core_rel}
            if it.tipo == "emprestimo" or (it.tipo == "diatonico" and it.escala != base):
                fontes.append(esc_longa(it.escala))
    if not P:
        P = {0, 4 if modo == "maior" else 3, 7}
    prio = PRIORIDADE_ESCALA[modo]
    melhor = min(prio, key=lambda e: (len(P - SETS[e]), prio.index(e)))
    misses = len(P - SETS[melhor])
    tn = nome_tonica(tom, hints)
    extras = sorted(P - SETS[base])
    return {
        "base": esc_longa(base),
        "notas_base": soletrar_escala(tn, ESCALAS[base]),
        "extras": [nome_nota_rel(e, tom, hints) for e in extras],
        "fontes": sorted(set(fontes)),
        "melhor": esc_longa(melhor) if misses == 0 and melhor != base else None,
        "notas_melhor": soletrar_escala(tn, ESCALAS[melhor]) if misses == 0 and melhor != base else None,
    }


# =============================================================================
# 10. APRESENTAÇÃO (TEXTO PURO E HTML)
# =============================================================================
COR = {"diatonico": "#d4edda", "emprestimo": "#ffe0b2", "dom_sec": "#f8d7da", "sub_dom": "#e1d5f5",
       "ii_sec": "#d6eaf8", "dim_sec": "#cfe8ee", "napolitano": "#fff3b0", "cromatico": "#e0e0e0",
       "dom_est": "#f5b7b1", "dom_mod": "#f1948a", "dim_pass": "#d5dbdb"}

# Uma cor por tonalidade (usada no "mapa tonal")
PALETA_TONS = ["#bbdefb", "#c8e6c9", "#ffe0b2", "#f8bbd0", "#d1c4e9", "#b2ebf2",
               "#fff59d", "#d7ccc8", "#ffccbc", "#dcedc8", "#b39ddb", "#80deea"]


def cores_dos_tons(res: dict) -> Dict[Tuple[int, str], str]:
    """Associa cada tonalidade detectada a uma cor (na ordem em que aparecem)."""
    mapa: Dict[Tuple[int, str], str] = {}
    for s in res["segmentos"]:
        if s["tom"] not in mapa:
            mapa[s["tom"]] = PALETA_TONS[len(mapa) % len(PALETA_TONS)]
    return mapa


def _fmt_escala_trecho(s, tom, hints, html=False):
    e = s["escala"]
    linhas = [f"Escala-base: {nome_nota_rel(0, tom, hints)} {e['base']} — {' '.join(e['notas_base'])}"]
    if e["extras"]:
        linhas.append("Notas fora da escala-base usadas nos acordes: " + " ".join(e["extras"])
                      + (f"  (origem: {', '.join(e['fontes'])})" if e["fontes"] else ""))
    if e.get("blues"):
        linhas.append(e["blues"])
    if e["melhor"]:
        linhas.append(f"Escala que reúne todas as notas dos acordes do trecho: "
                      f"{nome_nota_rel(0, tom, hints)} {e['melhor']} — {' '.join(e['notas_melhor'])}")
    return linhas


def texto_puro(res: dict, campos: bool = True) -> str:
    hints = res["hints"]
    out = []
    out.append("=" * 78)
    out.append("PROGRESSÃO: " + " ".join(a.simbolo for a in res["acordes"]))
    out.append("=" * 78)
    out.append("\nTONALIDADES DETECTADAS")
    for s in res["segmentos"]:
        a, b = s["ini"] + 1, s["fim"] + 1
        out.append(f"  • Compassos/acordes {a}–{b}: {nome_tom(s['tom'], hints)}")
        for l in _fmt_escala_trecho(s, s["tom"], hints):
            out.append("      " + l)
    if res["modulacoes"]:
        out.append("\nMODULAÇÕES")
        for m in res["modulacoes"]:
            out.append(f"  • (antes do acorde {m['em'] + 1}) {m['texto']}")
    else:
        out.append("\nMODULAÇÕES: nenhuma (progressão em um único tom)")
    out.append("\nANÁLISE ACORDE A ACORDE")
    for L in res["linhas"]:
        it, ch = L["interp"], L["acorde"]
        out.append(f"{L['i'] + 1:>3}. {ch.simbolo:<10} [{cifra_tom(L['tom'], hints):<4}] "
                   f"{it.grau:<14} {ROTULO[it.tipo].capitalize()}"
                   + (f" · {esc_longa(it.escala)}" if it.tipo in ('diatonico', 'emprestimo') else ""))
        out.append(f"       Função: {it.funcao}" + (f" | Escala do acorde: {it.esc_acorde}" if it.esc_acorde else ""))
        for n in L["notas"]:
            out.append(f"       - {n}")
    out.append("\nMAPA TONAL")
    for sg in res["segmentos"]:
        cif = " | ".join(res["acordes"][k].simbolo for k in range(sg["ini"], sg["fim"] + 1))
        out.append(f"  [{cifra_tom(sg['tom'], hints)}] {cif}")
    if campos:
        out.append("\nCAMPOS HARMÔNICOS DOS TONS DETECTADOS")
        vistos = set()
        for s in res["segmentos"]:
            if s["tom"] in vistos:
                continue
            vistos.add(s["tom"])
            tn = nome_tonica(s["tom"], hints)
            out.append(f"\n  {nome_tom(s['tom'], hints)}")
            for esc in CAMPOS_DO_MODO[s["tom"][1]]:
                notas, lin = campo_harmonico(tn, esc)
                out.append(f"    Escala {esc_longa(esc)}: {' '.join(notas)}")
                out.append("      Tríades : " + "  ".join(f"{r}={c}" for r, c, _, _ in lin))
                out.append("      Tétrades: " + "  ".join(f"{r}={c}" for _, _, r, c in lin))
    return "\n".join(out)


def html_resultado(res: dict, campos: bool = True) -> str:
    esc = _html.escape
    hints = res["hints"]
    cores = cores_dos_tons(res)
    h = []
    h.append("<div style='font-family:sans-serif;max-width:1100px'>")
    h.append(f"<h3>🎼 Progressão: {esc(' '.join(a.simbolo for a in res['acordes']))}</h3>")

    h.append("<h4>Tonalidades detectadas</h4><ul>")
    for s in res["segmentos"]:
        h.append(f"<li><b>Acordes {s['ini'] + 1}–{s['fim'] + 1}: {esc(nome_tom(s['tom'], hints))}</b><br>")
        for l in _fmt_escala_trecho(s, s["tom"], hints):
            h.append(f"<span style='font-size:90%'>{esc(l)}</span><br>")
        h.append("</li>")
    h.append("</ul>")
    h.append("<h4>Modulações</h4>")
    if res["modulacoes"]:
        h.append("<ul>" + "".join(f"<li>(antes do acorde {m['em'] + 1}) {esc(m['texto'])}</li>"
                                  for m in res["modulacoes"]) + "</ul>")
    else:
        h.append("<p>Nenhuma modulação: progressão em um único tom.</p>")

    h.append("<h4>Análise acorde a acorde</h4>")
    h.append("<table style='border-collapse:collapse;width:100%;font-size:14px'>")
    cab = ["#", "Acorde", "Tom", "Grau", "Classificação", "Função", "Escala do acorde", "Observações"]
    h.append("<tr>" + "".join(f"<th style='border:1px solid #8886;padding:4px 6px;text-align:left'>{c}</th>"
                              for c in cab) + "</tr>")
    for L in res["linhas"]:
        it, ch = L["interp"], L["acorde"]
        cls = ROTULO[it.tipo].capitalize()
        if it.tipo in ("diatonico", "emprestimo"):
            cls += f" · {esc_longa(it.escala)}"
        obs = "<br>".join(esc(n) for n in L["notas"])
        cel = "border:1px solid #8886;padding:4px 6px;vertical-align:top;"
        h.append(
            f"<tr><td style='{cel}'>{L['i'] + 1}</td>"
            f"<td style='{cel}'><b>{esc(ch.simbolo)}</b></td>"
            f"<td style='{cel}background:{cores[L['tom']]};color:#111'><b>{esc(cifra_tom(L['tom'], hints))}</b></td>"
            f"<td style='{cel}font-weight:bold'>{esc(it.grau)}</td>"
            f"<td style='{cel}background:{COR[it.tipo]};color:#111'>{esc(cls)}</td>"
            f"<td style='{cel}'>{esc(it.funcao)}</td>"
            f"<td style='{cel}'>{esc(it.esc_acorde)}</td>"
            f"<td style='{cel}font-size:90%'>{obs}</td></tr>")
    h.append("</table>")
    leg = "".join(f"<span style='background:{COR[k]};color:#111;padding:2px 8px;margin-right:6px;"
                  f"border-radius:4px;font-size:12px'>{v}</span>" for k, v in ROTULO.items())
    h.append(f"<p>{leg}</p>")

    # ---- MAPA TONAL: cifras coloridas por tonalidade -------------------------
    h.append("<h4>Mapa tonal (cada cor = uma tonalidade)</h4>")
    leg = "".join(f"<span style='background:{c};color:#111;padding:3px 10px;margin-right:6px;"
                  f"border-radius:4px;font-size:13px;border:1px solid #8886'><b>{esc(nome_tom(k, hints))}</b></span>"
                  for k, c in cores.items())
    h.append(f"<p>{leg}</p>")
    h.append("<div style='overflow-x:auto'><table style='border-collapse:collapse;font-size:14px'>")
    h.append("<tr>" + "".join(
        f"<td style='border:1px solid #8886;padding:6px 10px;text-align:center;background:{cores[L['tom']]};"
        f"color:#111'><b style='font-size:16px'>{esc(L['acorde'].simbolo)}</b><br>"
        f"<span style='font-size:12px'>{esc(L['interp'].grau)}</span><br>"
        f"<span style='font-size:11px'>{esc(cifra_tom(L['tom'], hints))}</span></td>"
        for L in res["linhas"]) + "</tr>")
    h.append("</table></div>")

    if campos:
        h.append("<h4>Campos harmônicos dos tons detectados</h4>")
        vistos = set()
        for s in res["segmentos"]:
            if s["tom"] in vistos:
                continue
            vistos.add(s["tom"])
            tn = nome_tonica(s["tom"], hints)
            h.append(f"<p><b>{esc(nome_tom(s['tom'], hints))}</b></p>")
            for e in CAMPOS_DO_MODO[s["tom"][1]]:
                notas, lin = campo_harmonico(tn, e)
                h.append(f"<p style='margin:2px 0'>Escala {esc(esc_longa(e))}: {esc(' '.join(notas))}</p>")
                cel = "border:1px solid #8886;padding:2px 8px;text-align:center;"
                h.append("<table style='border-collapse:collapse;font-size:13px;margin-bottom:10px'>")
                h.append("<tr><td style='" + cel + "'>Tríade</td>" +
                         "".join(f"<td style='{cel}'><b>{esc(r)}</b><br>{esc(c)}</td>" for r, c, _, _ in lin) + "</tr>")
                h.append("<tr><td style='" + cel + "'>Tétrade</td>" +
                         "".join(f"<td style='{cel}'><b>{esc(r)}</b><br>{esc(c)}</td>" for _, _, r, c in lin) + "</tr>")
                h.append("</table>")
    h.append("</div>")
    return "".join(h)


# =============================================================================
# 11. INTERFACE (CAIXA DE TEXTO NO COLAB / JUPYTER)
# =============================================================================
EXEMPLOS = [
    "Cmaj7 A7 Dm7 G7 Cmaj7 Fm6 Bb7 Cmaj7",
    "C Am F G7 C D7 G Em C D7 G",
    "Am Dm E7 Am C G7 C F Bb E7 Am",
    "Dm7 G7 Cmaj7 Ebmaj7 Ab7 Dbmaj7 Dm7b5 G7b9 Cm",
]


def iniciar_interface(padrao: str = EXEMPLOS[0]):
    try:
        import ipywidgets as W
        from IPython.display import display, clear_output, HTML
        get_ipython  # noqa  (garante que estamos num notebook)
    except Exception:
        print("Digite a progressão (acordes separados por espaço). Ex.:", EXEMPLOS[0])
        try:
            res = analisar(input("> "))
            print(texto_puro(res))
        except ValueError as e:
            print("Erro:", e)
        return

    caixa = W.Text(value=padrao, description="Acordes:", placeholder="Ex.: C Am Dm G7 C",
                   layout=W.Layout(width="95%"), style={"description_width": "70px"})
    botao = W.Button(description="Analisar", button_style="primary", icon="music")
    chk = W.Checkbox(value=True, description="Mostrar campos harmônicos", indent=False)
    saida = W.Output()

    def rodar(_=None):
        with saida:
            clear_output(wait=True)
            try:
                res = analisar(caixa.value)
                display(HTML(html_resultado(res, chk.value)))
            except ValueError as e:
                display(HTML(f"<p style='color:#c0392b'><b>Erro:</b> {_html.escape(str(e))}</p>"))

    botao.on_click(rodar)
    try:
        caixa.on_submit(rodar)
    except Exception:
        pass
    ajuda = W.HTML("<small>Separe os acordes por espaço. Aceita: C, Cm, C7, Cmaj7 (C7M, CΔ), Cm7, "
                   "Cm7(b5)/Cø, C°, Cdim7, C+, Csus4, C6, C9, C13, C7(b9), C7(#11), Cadd9, C/E (inversões)…</small>")
    display(W.VBox([caixa, W.HBox([botao, chk]), ajuda, saida]))
    rodar()


if __name__ == "__main__":
    iniciar_interface()
