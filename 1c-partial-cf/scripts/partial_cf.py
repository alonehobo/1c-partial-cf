#!/usr/bin/env python3
"""A small CF of chosen objects of a 1C configuration export (Designer XML) for
«Сравнить, объединить с конфигурацией из файла» and /MergeCfg.

The chosen objects go whole with their uuids; the objects their metadata refers
to go as stubs (the uuid, generated types, the properties free of references and
only the members referred to); the root keeps its uuid, name and languages; the
transfer subsystem _Перенос lists only the chosen objects. Next to the CF go the
/MergeCfg settings. References in BSL code are not followed.

The same rules as the C++ builder of the BslEdit MCP server (build
assemble_partial); the two are compared byte for byte.
Python 3.8+, standard library only; Windows and Linux.

  partial_cf.py --export <dir> --out <file.cf> [--objects Kind.Name ...] [--since <git rev>]
  partial_cf.py --export <dir> --source-only <dir> --objects ...   (the reduced export only)
"""

import argparse
import difflib
import heapq
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

# --- Kinds ----------------------------------------------------------------------

TYPE_FOLDERS = {
    "Catalog": "Catalogs", "Document": "Documents", "Enum": "Enums", "CommonModule": "CommonModules",
    "Report": "Reports", "DataProcessor": "DataProcessors", "ExchangePlan": "ExchangePlans",
    "ChartOfAccounts": "ChartsOfAccounts", "ChartOfCharacteristicTypes": "ChartsOfCharacteristicTypes",
    "ChartOfCalculationTypes": "ChartsOfCalculationTypes", "BusinessProcess": "BusinessProcesses", "Task": "Tasks",
    "InformationRegister": "InformationRegisters", "AccumulationRegister": "AccumulationRegisters",
    "AccountingRegister": "AccountingRegisters", "CalculationRegister": "CalculationRegisters",
    "CommonForm": "CommonForms", "CommonCommand": "CommonCommands", "CommonTemplate": "CommonTemplates",
    "CommonPicture": "CommonPictures", "CommonAttribute": "CommonAttributes", "Role": "Roles",
    "Subsystem": "Subsystems", "Constant": "Constants", "DocumentJournal": "DocumentJournals",
    "DefinedType": "DefinedTypes", "SessionParameter": "SessionParameters", "FunctionalOption": "FunctionalOptions",
    "FunctionalOptionsParameter": "FunctionalOptionsParameters", "EventSubscription": "EventSubscriptions",
    "ScheduledJob": "ScheduledJobs", "FilterCriterion": "FilterCriteria", "SettingsStorage": "SettingsStorages",
    "StyleItem": "StyleItems", "Style": "Styles", "Language": "Languages", "XDTOPackage": "XDTOPackages",
    "WebService": "WebServices", "HTTPService": "HTTPServices", "WSReference": "WSReferences",
    "DocumentNumerator": "DocumentNumerators", "Sequence": "Sequences", "ExternalDataSource": "ExternalDataSources",
    "Bot": "Bots", "Interface": "Interfaces", "IntegrationService": "IntegrationServices",
    "CommandGroup": "CommandGroups", "PaletteColor": "PaletteColors",
}
KINDS_SORTED = sorted(TYPE_FOLDERS)

MEMBER_KEYWORDS = {"Attribute", "TabularSection", "Form", "Command", "Template", "EnumValue",
                   "Dimension", "Resource", "AccountingFlag", "ExtDimensionAccountingFlag", "AddressingAttribute", "Column",
                   "Operation", "URLTemplate", "Method", "Recalculation", "Channel"}

# What a stub of a kind cannot go without (the Designer refuses the import).
REQUIRED_PROPERTIES = {
    "FunctionalOption": {"Location"}, "BusinessProcess": {"Task"},
    "AccountingRegister": {"ChartOfAccounts"},
    "CalculationRegister": {"ChartOfCalculationTypes", "Schedule", "ScheduleValue", "ScheduleDate"},
    "ChartOfAccounts": {"ExtDimensionTypes"}, "CommonCommand": {"Group"},
    "CommonAttribute": {"DataSeparationValue", "DataSeparationUse"},  # a separator names its session parameters
    "EventSubscription": {"Handler", "Source"}, "ScheduledJob": {"MethodName"},
}
REQUIRED_LISTS = {"DocumentJournal": {"RegisteredDocuments"}}
REQUIRED_CHILDREN = {
    "InformationRegister": ["Resource", "Dimension", "Attribute"], "AccumulationRegister": ["Resource"],
    "AccountingRegister": ["Resource"], "CalculationRegister": ["Resource"],
}

QUERY_KINDS = {
    "Справочник": "Catalog", "Документ": "Document", "Перечисление": "Enum",
    "РегистрСведений": "InformationRegister", "РегистрНакопления": "AccumulationRegister",
    "РегистрБухгалтерии": "AccountingRegister", "РегистрРасчета": "CalculationRegister",
    "ПланВидовХарактеристик": "ChartOfCharacteristicTypes", "ПланСчетов": "ChartOfAccounts",
    "ПланВидовРасчета": "ChartOfCalculationTypes", "ПланОбмена": "ExchangePlan",
    "БизнесПроцесс": "BusinessProcess", "Задача": "Task", "ЖурналДокументов": "DocumentJournal",
    "Константа": "Constant", "Последовательность": "Sequence", "КритерийОтбора": "FilterCriterion",
}
VIRTUAL_TABLES = {"СрезПоследних", "СрезПервых", "Остатки", "Обороты", "ОстаткиИОбороты",
                  "ДвиженияССубконто", "ОборотыДтКт", "Субконто", "ДанныеГрафика", "Изменения", "SliceLast", "SliceFirst", "Balance",
                  "Turnovers", "BalanceAndTurnovers", "RecordsWithExtDimensions", "DrCrTurnovers", "ExtDimensions", "ScheduleData", "Changes"}
AS_WORDS = {"КАК", "как", "Как", "AS", "as", "As"}
REF_WORDS = {"Ссылка", "Ref"}
PREDEFINED = "@predefined"  # a query path to a predefined item: [PREDEFINED, name]
SPACE = " \t\r\n\x0b\x0c"  # the white space of a query, ASCII only as in the C++ builder
OPEN_PROPERTIES = ("DefaultForm", "MainDataCompositionSchema")  # what StandardCommand.Open of a stub needs
# Modules of a stub stay out of the CF: merged with the base first, a stub module still put
# the methods of the export into the base module and added an end of line to a module
# without one (8.3.27). A property of a stub that differs from the export gets DoNotMerge;
# the Designer refuses a rule for a property equal in the base and the CF.
STUB_MODULES = ("ObjectModule", "ManagerModule", "RecordSetModule", "ValueManagerModule", "CommandModule", "Module")
KEPT_MODULES = ("/Ext/CommandModule.bsl", "/Ext/Form/Module.bsl")  # of a command or a form a stub keeps
CONSTANTS_SET = "@constants"
ALL_FIELDS = "@all"  # a query path Источник.*: every field of the object  # the type of a form attribute НаборКонстант: its fields are constants
# A resource of a virtual table of a register (КоличествоОстаток, СуммаОборотДт): the suffix
# goes, longest first, then Дт/Кт of an accounting dimension (СчетДт, Субконто1Кт is no member).
RESOURCE_SUFFIXES = sorted((
    "НачальныйРазвернутыйОстаток", "КонечныйРазвернутыйОстаток", "НачальныйОстаток", "КонечныйОстаток",
    "Остаток", "Оборот", "Приход", "Расход", "ВстречныйОборот",
    "OpeningSplittedBalance", "ClosingSplittedBalance", "OpeningBalance", "ClosingBalance",
    "Balance", "Turnover", "Receipt", "Expense", "CorrTurnover"), key=len, reverse=True)
SIDE_SUFFIXES = ("Дт", "Кт", "Dr", "Cr")
REGISTER_KINDS = ("AccumulationRegister", "AccountingRegister", "CalculationRegister", "InformationRegister")


def fold(s):
    """The query language ignores case: ASCII and Cyrillic letters folded, the rest kept,
    the same as the C++ builder."""
    return "".join(chr(ord(c) + 32) if "A" <= c <= "Z" or "А" <= c <= "Я" else "ё" if c == "Ё" else c for c in s)


QUERY_KINDS_FOLDED = {fold(k): v for k, v in QUERY_KINDS.items()}
QUERY_KINDS_FOLDED.update({fold(k): k for k in TYPE_FOLDERS if k != "Language"})
# Words of the query language that never name a field or an alias.
QUERY_KEYWORDS = {fold(w) for w in (
    "ВЫБРАТЬ ИЗ ГДЕ ЛЕВОЕ ПРАВОЕ ВНУТРЕННЕЕ ПОЛНОЕ ВНЕШНЕЕ СОЕДИНЕНИЕ ПО СГРУППИРОВАТЬ УПОРЯДОЧИТЬ ОБЪЕДИНИТЬ ВСЕ "
    "ИМЕЮЩИЕ ИТОГИ ДЛЯ ИЗМЕНЕНИЯ ИНДЕКСИРОВАТЬ ВЫБОР КОГДА ТОГДА ИНАЧЕ КОНЕЦ И ИЛИ НЕ В ЕСТЬ NULL КАК РАЗРЕШЕННЫЕ "
    "РАЗЛИЧНЫЕ ПЕРВЫЕ ИЕРАРХИИ ССЫЛКА МЕЖДУ ПОДОБНО СПЕЦСИМВОЛ ПОМЕСТИТЬ УНИЧТОЖИТЬ АВТОУПОРЯДОЧИВАНИЕ ВОЗР УБЫВ ОБЩИЕ "
    "ТОЛЬКО ПЕРИОДАМИ ИСТИНА ЛОЖЬ НЕОПРЕДЕЛЕНО ЗНАЧЕНИЕ ВЫРАЗИТЬ ТИП ТИПЗНАЧЕНИЯ ЕСТЬNULL ПРЕДСТАВЛЕНИЕ "
    "ПРЕДСТАВЛЕНИЕССЫЛКИ КОЛИЧЕСТВО СУММА МАКСИМУМ МИНИМУМ СРЕДНЕЕ ПОДСТРОКА "
    "SELECT FROM WHERE LEFT RIGHT INNER FULL OUTER JOIN ON GROUP BY ORDER UNION ALL HAVING TOTALS FOR UPDATE INDEX "
    "CASE WHEN THEN ELSE END AND OR NOT IN IS NULL AS ALLOWED DISTINCT TOP HIERARCHY REFS BETWEEN LIKE ESCAPE INTO DROP "
    "AUTOORDER ASC DESC OVERALL ONLY PERIODS TRUE FALSE UNDEFINED VALUE CAST TYPE VALUETYPE ISNULL PRESENTATION "
    "REFPRESENTATION COUNT SUM MAX MIN AVG SUBSTRING").split()}


class BuildError(Exception):
    """A wrong selection or export; the message is for the user."""


# --- References -----------------------------------------------------------------

def is_ident(ch):
    return ch >= "\x80" or ("0" <= ch <= "9") or ("A" <= ch <= "Z") or ("a" <= ch <= "z") or ch == "_"


def is_standard_member(m):
    return m.startswith("Standard")


class Ref:
    """Catalog.X.Attribute.Y in a descriptor or a form; cfg:CatalogRef.X; style:X."""
    __slots__ = ("kind", "name", "member", "member_name", "predefined")

    def __init__(self, kind, name, member="", member_name="", predefined=""):
        self.kind, self.name, self.member, self.member_name, self.predefined = kind, name, member, member_name, predefined


def kind_of(token):
    """The kind a type or reference token names, and whether it is the kind itself."""
    if token in TYPE_FOLDERS:
        return token, True
    if token == "Characteristic":
        return "ChartOfCharacteristicTypes", False
    best = ""
    for k in KINDS_SORTED:
        if len(token) > len(k) and token.startswith(k) and "A" <= token[len(k)] <= "Z" and len(k) > len(best):
            best = k
    return best, False


_ID = "0-9A-Za-z_\u0080-\U0010ffff"
# A run of identifier characters that starts a word (not after another one or a dot):
# after "style:" a style item, else one starting with A-Z and followed by a dot.
_CANDIDATE = re.compile("(?<![." + _ID + "])(?:(?<=style:)([" + _ID + "]+)|([A-Z][" + _ID + "]*)(?=\\.))")
_SEGMENTS = re.compile("(?:\\.[" + _ID + "]+){1,5}")


def scan(text):
    out = []
    for m in _CANDIDATE.finditer(text):
        if m.group(1) is not None:
            out.append(Ref("StyleItem", m.group(1)))
            continue
        token = m.group(2)
        kind, exact = kind_of(token)
        if not kind:
            continue
        chain = _SEGMENTS.match(text, m.end())
        if not chain:
            continue
        seg = chain.group(0)[1:].split(".")
        r = Ref(kind, seg[0])
        if exact and len(seg) >= 3 and seg[1] in MEMBER_KEYWORDS:
            r.member, r.member_name = seg[1], seg[2]
        elif exact and len(seg) >= 4 and seg[1] == "StandardCommand" and seg[2] == "OpenByValue":
            r.member, r.member_name = "*", seg[3]
        elif exact and len(seg) >= 3 and seg[1] == "StandardCommand":
            r.member, r.member_name = seg[1], seg[2]
        elif exact and len(seg) == 2 and not is_standard_member(seg[1]) and seg[1] not in MEMBER_KEYWORDS and seg[1] != "EmptyRef":
            r.predefined = seg[1]
        elif not exact and len(seg) >= 2 and "TabularSection" in token:
            r.member, r.member_name = "TabularSection", seg[1]
        out.append(r)
        if r.member == "*" and len(seg) >= 4 and seg[1] == "StandardCommand" and seg[2] == "OpenByValue":
            out.append(Ref(kind, seg[0], "StandardCommand", "OpenByValue"))
    return out


# --- Elements -------------------------------------------------------------------

class Span:
    """<tag …>inner</tag> or <tag …/>; end is past the closing tag."""
    __slots__ = ("tag", "open", "inner", "inner_end", "end")

    def __init__(self, tag, open_, inner):
        self.tag, self.open, self.inner, self.inner_end, self.end = tag, open_, inner, 0, 0


_TAG_NAME = re.compile("[^ \t\n\r\x0b\x0c/]*")


_children_cache = {}


def children(text, frm, to):
    """The direct child elements in text[frm, to). Designer dumps carry neither
    CDATA nor comments inside descriptors; a comment or a declaration is skipped.
    Stubs are rebuilt on every pass from the same texts: the result is cached."""
    k = (text, frm, to)
    out = _children_cache.get(k)
    if out is None:
        out = _children_cache[k] = _children(text, frm, to)
    return out


def _children(text, frm, to):
    out = []
    top = None   # the open direct child; nested elements are only counted
    depth = 0
    i = frm
    while i < to:
        lt = text.find("<", i)
        if lt < 0 or lt >= to:
            break
        if text.startswith("<!--", lt):
            e = text.find("-->", lt)
            i = to if e < 0 else e + 3
            continue
        nxt = text[lt + 1] if lt + 1 < len(text) else ""
        if nxt in ("?", "!"):
            e = text.find(">", lt)
            i = to if e < 0 else e + 1
            continue
        gt = text.find(">", lt)
        if gt < 0 or gt >= to:
            break
        if nxt == "/":
            if depth:
                depth -= 1
                if not depth:
                    top.inner_end, top.end = lt, gt + 1
                    out.append(top)
            i = gt + 1
            continue
        if depth:
            if text[gt - 1] != "/":
                depth += 1
            i = gt + 1
            continue
        m = _TAG_NAME.match(text, lt + 1, gt)
        s = Span(m.group(0), lt, gt + 1)
        if text[gt - 1] == "/":
            s.inner = s.inner_end = s.end = gt + 1
            out.append(s)
        else:
            top = s
            depth = 1
        i = gt + 1
    return out


def find(spans, tag):
    for s in spans:
        if s.tag == tag:
            return s
    return None


def member_name(text, s):
    """The <Name> of a member element, or the text of a simple one (<Form>Имя</Form>)."""
    kids = children(text, s.inner, s.inner_end)
    if not kids:
        return text[s.inner:s.inner_end]
    p = find(kids, "Properties")
    if p:
        nm = find(children(text, p.inner, p.inner_end), "Name")
        if nm:
            return text[nm.inner:nm.inner_end]
    return ""


def object_element(text):
    """The object element of a descriptor: MetaDataObject → Catalog."""
    root = find(children(text, 0, len(text)), "MetaDataObject")
    if not root:
        return None
    kids = children(text, root.inner, root.inner_end)
    return kids[0] if kids else None


# --- Files ----------------------------------------------------------------------

def long_path(path):
    """On Windows the \\\\?\\ form of a path, so that files past MAX_PATH (a deep
    _files picture of a template below a temporary folder) open whatever the
    LongPathsEnabled setting."""
    if os.name != "nt" or path.startswith("\\\\?\\"):
        return path
    path = os.path.abspath(path)
    return "\\\\?\\UNC\\" + path[2:] if path.startswith("\\\\") else "\\\\?\\" + path


def read_file(path):
    """A file that does not open is an error: an empty text would go into the CF
    as a broken descriptor or picture."""
    try:
        with open(long_path(path), "rb") as f:
            return f.read().decode("utf-8", "surrogateescape")
    except OSError as e:
        raise BuildError("Не читается " + path + ": " + str(e.strerror or e))


def write_file(path, text):
    path = long_path(path)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(text.encode("utf-8", "surrogateescape"))


def has_text(path):
    """A module with something but white space in it; absent is empty."""
    if not os.path.isfile(long_path(path)):
        return False
    return bool(read_file(path).lstrip("﻿").strip(" \t\r\n\x0b\x0c"))


def content_of(text):
    """The first Content element of a descriptor as written, '' without one."""
    a = text.find("<Content")
    while a >= 0 and text[a + 8:a + 9] not in (">", "/"):
        a = text.find("<Content", a + 1)
    if a < 0:
        return ""
    if text.startswith("<Content/>", a):
        return "<Content/>"
    e = text.find("</Content>", a)
    return text[a:e + 10] if e >= 0 else ""


def escape(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


def key_of(kind, name):
    return kind + "." + name


def split_key(key):
    dot = key.find(".")
    return (key, "") if dot < 0 else (key[:dot], key[dot + 1:])


def descriptor_rel(key):
    kind, name = split_key(key)
    folder = TYPE_FOLDERS.get(kind)
    return folder + "/" + name + ".xml" if folder else ""


def native(src, rel):
    return long_path(os.path.join(src, *rel.split("/")))


def exists(src, key):
    rel = descriptor_rel(key)
    return bool(rel) and os.path.isfile(native(src, rel))


def _listing(path):
    try:
        with os.scandir(path) as it:
            return sorted(it, key=lambda e: e.name)
    except OSError:
        return []


def files_below(src, key):
    """Kinds/X.xml and every file below Kinds/X, relative to the export, '/'. The files
    below go by name: the order decides who a stub names as its referrer."""
    kind, name = split_key(key)
    folder = TYPE_FOLDERS.get(kind)
    if not folder or not os.path.isfile(native(src, folder + "/" + name + ".xml")):
        return []
    below = []

    def walk(path, rel):
        for e in _listing(path):
            if e.is_dir():
                walk(e.path, rel + e.name + "/")
            elif e.is_file():
                below.append(rel + e.name)

    walk(native(src, folder + "/" + name), folder + "/" + name + "/")
    return [folder + "/" + name + ".xml"] + sorted(below)


def stable_uuid(seed):
    """A uuid stable for the configuration and the subsystem name, so a rebuilt CF compares the same."""
    m = (1 << 64) - 1
    a, b = 1469598103934665603, 1099511628211 ^ 0x9e3779b97f4a7c15
    for c in seed.encode("utf-8", "surrogateescape"):
        a = ((a ^ c) * 1099511628211) & m
        b = ((b ^ c) * 0x100000001b3 + 0x7f4a7c15) & m
    return "%08x-%04x-4%03x-%04x-%012x" % (a >> 32, (a >> 16) & 0xffff, a & 0xfff, ((b >> 48) & 0x3fff) | 0x8000, b & 0xffffffffffff)


# --- Stubs ----------------------------------------------------------------------

class Stub:
    __slots__ = ("reason", "members", "predefined", "based_on", "by_value")

    def __init__(self):
        self.reason = ""          # the object that refers to it first
        self.members = set()      # (keyword, name); keyword * for a name of a data path
        self.predefined = False
        self.based_on = False     # its CreateBasedOn command is used: BasedOn stays non-empty
        self.by_value = False     # an OpenByValue command is used: every master dimension stays


def _indent_before(text, inner, inner_end):
    nl = text.rfind("\n", 0, inner_end + 1)
    return text[nl:inner_end] if nl >= 0 and nl > inner else ""


def clean_properties(text, props, self_key, keep_kind, present=frozenset(), based_on=False, own=frozenset()):
    """A property referring to another object, or to a non-standard member of its own,
    becomes empty, but the default form or the main schema the stub keeps (own); Name, Synonym, Comment, Type and the required ones stay. Of a list the
    items naming only objects of the CF stay."""
    kind = split_key(self_key)[0]

    def foreign(part, tag):
        for r in scan(part):
            if keep_kind and r.kind == keep_kind:
                continue
            if key_of(r.kind, r.name) == self_key and (not r.member or is_standard_member(r.member)) and not r.predefined:
                continue
            if key_of(r.kind, r.name) == self_key and tag in OPEN_PROPERTIES and (r.member, r.member_name) in own:
                continue
            return True
        return False

    out = [text[props.open:props.inner]]
    pos = props.inner
    for p in children(text, props.inner, props.inner_end):
        out.append(text[pos:p.open])
        keep_all = p.tag in ("Name", "Synonym", "Comment", "Type") or p.tag in REQUIRED_PROPERTIES.get(kind, ())
        if keep_all or not foreign(text[p.inner:p.inner_end], p.tag):
            out.append(text[p.open:p.end])
            pos = p.end
            continue
        items = ""
        last = p.inner
        lst = children(text, p.inner, p.inner_end)
        is_list = bool(lst)
        for item in lst:
            gap, body = text[last:item.open], text[item.open:item.end]
            last = item.end
            if item.tag != "xr:Item":
                is_list = False
                break
            if all(key_of(r.kind, r.name) in present for r in scan(body)):
                items += gap + body
        non_empty = (based_on and p.tag == "BasedOn") or p.tag in REQUIRED_LISTS.get(kind, ())
        if is_list and non_empty and not items:
            items = text[p.inner:lst[0].end]
        if not is_list or not items:
            out.append("<" + p.tag + "/>")
        else:
            out.append(text[p.open:p.inner] + items + _indent_before(text, p.inner, p.inner_end) + "</" + p.tag + ">")
        pos = p.end
    out.append(text[pos:props.end])
    return "".join(out)


def stub_descriptor(text, key, stub, present, keep_below):
    """The descriptor of a stub; the files below it that it keeps go to keep_below."""
    obj = object_element(text)
    if not obj:
        raise BuildError("not a descriptor: " + key)
    out = [text[:obj.inner]]
    pos = obj.inner
    for s in children(text, obj.inner, obj.inner_end):
        out.append(text[pos:s.open])
        if s.tag == "Properties":
            out.append(clean_properties(text, s, key, "", present, stub.based_on, stub.members))
        elif s.tag == "ChildObjects":
            kept = ""
            last = s.inner
            kids = children(text, s.inner, s.inner_end)
            names = [member_name(text, m) for m in kids]

            def wanted(i):
                # /MergeCfg matches the OpenByValue commands by their order, so every master dimension stays
                return ((kids[i].tag, names[i]) in stub.members or ("*", names[i]) in stub.members
                        or (stub.by_value and kids[i].tag == "Dimension" and "<Master>true</Master>" in text[kids[i].open:kids[i].end]))

            required = REQUIRED_CHILDREN.get(split_key(key)[0], [])
            extra = len(kids)
            satisfied = not required
            i = 0
            while i < len(kids) and not satisfied:
                satisfied = wanted(i) and kids[i].tag in required
                i += 1
            for tag in required:
                if satisfied or extra < len(kids):
                    break
                for i, m in enumerate(kids):
                    if m.tag == tag:
                        extra = i
                        break
            for i, m in enumerate(kids):
                name = names[i]
                gap = text[last:m.open]
                last = m.end
                if not wanted(i) and i != extra:
                    continue
                kept += gap + text[m.open:m.end]
                if m.tag == "Form":
                    keep_below += ["Forms/" + name + ".xml", "Forms/" + name + "/"]
                elif m.tag == "Template":
                    keep_below += ["Templates/" + name + ".xml", "Templates/" + name + "/"]
                elif m.tag == "Command":
                    keep_below.append("Commands/" + name + "/")
            if not kept:
                out.append("<ChildObjects/>")
            else:
                out.append("<ChildObjects>" + kept + _indent_before(text, s.inner, s.inner_end) + "</ChildObjects>")
        else:
            out.append(text[s.open:s.end])
        pos = s.end
    if stub.predefined:
        keep_below.append("Ext/Predefined.xml")
    out.append(text[pos:])
    return "".join(out)


# --- Data paths of forms -----------------------------------------------------------

class Member:
    __slots__ = ("tag", "types", "columns")

    def __init__(self, tag, types):
        self.tag, self.types, self.columns = tag, types, {}


def type_keys(text, owner):
    out = set()
    p = find(children(text, owner.inner, owner.inner_end), "Properties")
    if p:
        t = find(children(text, p.inner, p.inner_end), "Type")
        if t:
            out.update(key_of(r.kind, r.name) for r in scan(text[t.inner:t.inner_end]))
    return out


def index_members(text, child_objects):
    out = {}
    for m in children(text, child_objects.inner, child_objects.inner_end):
        kids = children(text, m.inner, m.inner_end)
        if not kids:
            continue  # <Form>Имя</Form>
        member = Member(m.tag, type_keys(text, m))
        c = find(kids, "ChildObjects")
        if c:
            member.columns = index_members(text, c)
        out[member_name(text, m)] = member
    return out


def attribute_value(text, open_, close, name):
    k = " " + name + '="'
    at = text.find(k, open_)
    if at < 0 or at >= close:
        return ""
    frm = at + len(k)
    to = text.find('"', frm)
    return "" if to < 0 else text[frm:to]


def query_refs(query, fields=None):
    """Sources of a dynamic list query (Справочник.Партнеры КАК П) and the fields read
    through them (П.Менеджер.Имя): (object, path); a tabular section source starts the path.
    A field without an alias (ВЫБРАТЬ Сотрудник ИЗ …) is tried on every source of the
    text, nested queries included: a member kept in excess is harmless, a missing one
    fails the whole query in the import. fields, when given, gets the fields the text
    names with КАК: their folded name → [(object, path)]."""
    words = []  # (dotted chain, start, end); strings, comments and parameters skipped
    n = len(query)

    def skip_string(i):
        e = query.find('"', i + 1)
        return n if e < 0 else e + 1

    def skip_space(i):
        while i < n:
            if query[i] in SPACE:
                i += 1
            elif query.startswith("//", i):
                e = query.find("\n", i)
                i = n if e < 0 else e
            else:
                break
        return i

    def skip_parens(i):  # query[i] == "("; past the matching ")"
        depth = 0
        while i < n:
            c = query[i]
            if c == '"':
                i = skip_string(i)
                continue
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    return i + 1
            i += 1
        return n

    i = 0
    while i < n:
        c = query[i]
        if c == '"':
            i = skip_string(i)
            continue
        if c == "/" and i + 1 < n and query[i + 1] == "/":
            e = query.find("\n", i)
            i = n if e < 0 else e
            continue
        if c == "&":
            while i < n and (query[i] == "&" or is_ident(query[i])):
                i += 1
            continue
        if not is_ident(c) or "0" <= c <= "9":
            i += 1
            continue
        seg = []
        j = i
        while True:
            e = j
            while e < n and is_ident(query[e]):
                e += 1
            seg.append(query[j:e])
            if e + 1 < n and query[e] == "." and is_ident(query[e + 1]):
                j = e + 1
            else:
                j = e
                break
        words.append((seg, i, j))
        i = j
    at = {start: k for k, (_, start, _) in enumerate(words)}

    def kind_word(w):
        return QUERY_KINDS_FOLDED.get(fold(w), "")

    def single(k):
        return words[k][0][0] if k is not None and len(words[k][0]) == 1 else ""

    out, alias, sources, seen, used = [], {}, [], set(), set()
    ends = {end: k for k, (_, _, end) in enumerate(words)}
    value_of = {}  # the word an expression starts at → (object, path) it yields
    if fields is None:
        fields = {}

    def add(key, path):
        if (key, tuple(path)) not in seen:
            seen.add((key, tuple(path)))
            out.append((key, path))

    def named(k):
        """The name after КАК that follows the word k, or ""."""
        word = single(at.get(skip_space(words[k][2])))
        if not word or fold(word) not in ("как", "as"):
            return ""
        return single(at.get(skip_space(words[at[skip_space(words[k][2])]][2])))

    def name_field(name, key, path):
        bound = fields.setdefault(fold(name), [])
        if (key, path) not in bound:
            bound.append((key, path))

    def word_before(text):
        b = len(text)
        while b > 0 and is_ident(text[b - 1]):
            b -= 1
        return fold(text[b:])

    # Names given with КАК: an alias may be a word of a kind (… КАК Задача); then a chain
    # of that word is a source only after ИЗ or СОЕДИНЕНИЕ.
    named_as = {fold(named(k)) for k in range(len(words)) if named(k)}
    for k, (seg, start, end) in enumerate(words):
        kind = kind_word(seg[0]) if len(seg) >= 2 else ""
        if not kind:
            continue
        before = query[:start].rstrip(SPACE)
        used.add(k)
        key = key_of(kind, seg[1])
        if before.endswith("(") and fold(before[:-1].rstrip(SPACE)[-8:]).endswith(("значение", "value")):
            # ЗНАЧЕНИЕ(Справочник.Валюты.Рубль): a predefined item, an enum value is a member
            add(key, [])
            if len(seg) >= 3 and fold(seg[2]) not in ("пустаяссылка", "emptyref"):
                add(key, [seg[2]] if kind == "Enum" else [PREDEFINED, seg[2]])
            close = skip_space(end)
            if close < n and query[close] == ")":  # ЗНАЧЕНИЕ(…) КАК Организация: a field of that type
                word = single(at.get(skip_space(close + 1)))
                if word and fold(word) in ("как", "as"):
                    name = single(at.get(skip_space(words[at[skip_space(close + 1)]][2])))
                    if name:
                        name_field(name, key, [])
            continue
        prev = word_before(before)
        if not prev and before.endswith("("):
            prev = "(" + word_before(before[:-1].rstrip(SPACE))
        if prev in ("как", "as", "ссылка", "refs", "(тип", "(type"):
            # A type, not a source: ВЫРАЗИТЬ(Д.Основание КАК Документ.Заказ).Склад,
            # Т.Документ ССЫЛКА Документ.Заказ, ТИП(Документ.Заказ)
            add(key, [])
            close = skip_space(end)
            if prev in ("как", "as") and close + 1 < n and query[close] == ")" and query[close + 1] == ".":
                k2 = at.get(close + 2)
                if k2 is not None:
                    used.add(k2)
                    add(key, list(words[k2][0]))
                    if named(k2):
                        name_field(named(k2), key, list(words[k2][0]))
                    # the value of ВЫРАЗИТЬ(…).Склад, for ТОГДА ВЫРАЗИТЬ(…).Склад … КОНЕЦ КАК Склад
                    depth, o = 0, close
                    while o >= 0:
                        depth += query[o] == ")"
                        depth -= query[o] == "("
                        if depth == 0:
                            break
                        o -= 1
                    first = ends.get(query[:max(o, 0)].rstrip(SPACE).__len__())
                    if first is not None:
                        value_of[first] = [(key, list(words[k2][0]))]
            continue
        if fold(seg[0]) in named_as and prev not in ("из", "from", "соединение", "join"):
            used.discard(k)  # a field through an alias named as a kind (Задача.Исполнитель)
            continue
        section = [seg[2]] if len(seg) >= 3 and seg[2] not in VIRTUAL_TABLES else []
        if (key, section) not in sources:
            sources.append((key, section))
        add(key, section)
        # The alias: past the parameters of a virtual table, after КАК or alone.
        name = seg[-1]
        pos = skip_space(end)
        if pos < n and query[pos] == "(":
            pos = skip_space(skip_parens(pos))
        nxt = at.get(pos)
        word = single(nxt)
        if word and fold(word) in ("как", "as"):
            following = single(at.get(skip_space(words[nxt][2])))
            if following:
                name = following
        elif word and fold(word) not in QUERY_KEYWORDS:
            name = word
        bound = alias.setdefault(fold(name), [])  # the parts of ОБЪЕДИНИТЬ reuse an alias
        if (key, section) not in bound:
            bound.append((key, section))
    for k, (seg, _, end) in enumerate(words):
        if k in used:
            continue
        head = fold(seg[0])
        if head in alias:
            if len(seg) == 1 and query.startswith(".*", end):  # РегистрСведений.*: every field
                paths = [(key, section + [ALL_FIELDS]) for key, section in alias[head] if not section]
            else:
                paths = [(key, section + seg[1:]) for key, section in alias[head]] if len(seg) >= 2 else []
        elif len(seg) == 1 and head in QUERY_KEYWORDS:
            continue
        else:
            # A field without an alias, or through the alias of a nested query or a temporary
            # table (Вложенный.Ссылка.Поле): the chain and its tail are tried on every source,
            # and a field named earlier with КАК goes on through what it was named after.
            paths = [(key, section + seg) for key, section in sources]
            if len(seg) >= 2:
                paths += [(key, section + seg[1:]) for key, section in sources]
            for at_seg in (0, 1):
                if at_seg < len(seg) and (at_seg == 0 or len(seg) >= 2) and fold(seg[at_seg]) in fields:
                    paths += [(key, path + seg[at_seg + 1:]) for key, path in list(fields[fold(seg[at_seg])])]
        for key, path in paths:
            add(key, path)
        value_of[k] = paths
        name = named(k)
        if name:
            for key, path in paths:
                name_field(name, key, path)
    # ВЫБОР КОГДА … ТОГДА Т.Склад ИНАЧЕ ВЫРАЗИТЬ(…).Склад КОНЕЦ КАК Склад: the field goes
    # through the values of its branches.
    cases = []
    for k, (seg, _, _) in enumerate(words):
        w = fold(seg[0]) if len(seg) == 1 else ""
        if w in ("выбор", "case"):
            cases.append([])
        elif w in ("тогда", "иначе", "then", "else") and cases and k + 1 < len(words):
            cases[-1] += value_of.get(k + 1, [])
        elif w in ("конец", "end") and cases:
            paths = cases.pop()
            name = named(k)
            if name:
                for key, path in paths:
                    name_field(name, key, path)
    return out


def module_values(text):
    """ЗНАЧЕНИЕ(Перечисление.Статусы.ВРаботе) in the query texts of a module: the import checks
    them, so the value or the predefined item must be in the CF. (object, path) as query_refs."""
    out = []
    n = len(text)
    i = text.find("(")
    while i >= 0:
        b = i
        while b > 0 and text[b - 1] in SPACE:
            b -= 1
        a = b
        while a > 0 and is_ident(text[a - 1]):
            a -= 1
        if fold(text[a:b]) in ("значение", "value") and (a == 0 or text[a - 1] != "."):
            j = i + 1
            while j < n and text[j] in SPACE:
                j += 1
            e = j
            while e < n and (is_ident(text[e]) or text[e] == "."):
                e += 1
            k = e
            while k < n and text[k] in SPACE:
                k += 1
            if k < n and text[k] == ")" and text[j:e].count(".") == 2:
                for r in query_refs("ЗНАЧЕНИЕ(" + text[j:e] + ")"):
                    if r not in out:
                        out.append(r)
        i = text.find("(", i + 1)
    return out


_ENTITIES = (("&lt;", "<"), ("&gt;", ">"), ("&amp;", "&"), ("&quot;", '"'), ("&apos;", "'"))


def xml_text(s):
    o = []
    i = 0
    while i < len(s):
        if s[i] != "&":
            o.append(s[i])
            i += 1
            continue
        for e, c in _ENTITIES:
            if s.startswith(e, i):
                o.append(c)
                i += len(e)
                break
        else:
            o.append("&")
            i += 1
    return "".join(o)


def _dotted(t):
    if "." not in t:
        return False
    if any(not is_ident(c) and c != "." for c in t):
        return False
    return t[0] != "." and t[-1] != "."


def form_paths(form):
    """Data paths of a managed form from its attributes: (types, rest of the path).
    Items.Таблица.CurrentData.Колонка goes through the DataPath of the item; a column
    of a value table or tree attribute (Дерево.Вид.Единица) through the column's type."""
    out = []
    root = find(children(form, 0, len(form)), "Form")
    if not root:
        return out
    attrs, columns, list_fields = {}, {}, {}
    a = find(children(form, root.inner, root.inner_end), "Attributes")
    if a:
        for at in children(form, a.inner, a.inner_end):
            name = attribute_value(form, at.open, at.inner, "name")
            kids = children(form, at.inner, at.inner_end)
            types = set()
            t = find(kids, "Type")
            if t:
                types.update(key_of(r.kind, r.name) for r in scan(form[t.inner:t.inner_end]))
                if "cfg:ConstantsSet<" in form[t.inner:t.inner_end]:
                    types.add(CONSTANTS_SET)
            cols = find(kids, "Columns")
            if cols and name:
                for col in children(form, cols.inner, cols.inner_end):
                    ct = find(children(form, col.inner, col.inner_end), "Type")
                    col_types = {key_of(r.kind, r.name) for r in scan(form[ct.inner:ct.inner_end])} if ct else set()
                    col_name = attribute_value(form, col.open, col.inner, "name")
                    if col_name and col_types:
                        columns[name + "." + col_name] = col_types
            settings = find(kids, "Settings")
            if settings:  # a dynamic list: its main table and query
                opts = children(form, settings.inner, settings.inner_end)
                main = find(opts, "MainTable")
                if main:
                    types.update(key_of(r.kind, r.name) for r in scan(form[main.inner:main.inner_end]))
                q = find(opts, "QueryText")
                if q:
                    named = list_fields.setdefault(name, {}) if name else {}
                    for key, path in query_refs(xml_text(form[q.inner:q.inner_end]), named):
                        out.append(({key}, path))
            if name and types:
                attrs[name] = types
    item_paths = {}
    at = form.find("<DataPath>")
    while at >= 0:
        end = form.find("</DataPath>", at)
        named = form.rfind(' name="', 0, at + 7)
        if end >= 0 and named >= 0:
            q = form.find('"', named + 7)
            item_paths[form[named + 7:q] if q >= 0 else form[named + 7:]] = form[at + 10:end]
        at = form.find("<DataPath>", at + 1)
    # Element texts (<DataPath>Объект.Счёт</DataPath>) and attribute values (table="Объект.Товары").
    texts = []
    gt = form.find(">")
    while gt >= 0:
        lt = form.find("<", gt)
        if lt < 0:
            break
        texts.append(form[gt + 1:lt])
        gt = form.find(">", gt + 1)
    q = form.find('="')
    while q >= 0:
        e = form.find('"', q + 2)
        if e < 0:
            break
        texts.append(form[q + 2:e])
        q = form.find('="', q + 2)
    seen = set()
    for t in texts:
        if len(t.encode("utf-8", "surrogateescape")) < 3 or not _dotted(t) or t in seen:
            continue
        seen.add(t)
        seg = t.split(".")
        if seg[0] == "Items" and len(seg) >= 4 and seg[2] == "CurrentData" and seg[1] in item_paths:
            seg = item_paths[seg[1]].split(".") + seg[3:]
        if len(seg) >= 3 and seg[0] in list_fields:  # Список.Организация.ИНН: the field named in the query
            for key, path in list_fields[seg[0]].get(fold(seg[1]), []):
                out.append(({key}, path + seg[2:]))
        if len(seg) >= 3 and seg[0] + "." + seg[1] in columns:
            out.append((columns[seg[0] + "." + seg[1]], seg[2:]))
        if seg[0] not in attrs or len(seg) < 2:
            continue
        out.append((attrs[seg[0]], seg[1:]))
    return out


# --- Build ----------------------------------------------------------------------

class Result:
    def __init__(self, subsystem):
        self.selected = []   # Catalog.X in the order given
        self.stubs = {}      # Catalog.Y → Stub
        self.subsystem = subsystem
        self.configuration = ""  # the name of the root
        self.files = []      # written, relative to the output
        self.rules = {}      # a stub or a child it keeps → its properties with DoNotMerge
        self.patched = {}    # an object moved by module patches → its settings entries (patch_entries)


def build(src, dst, objects, subsystem="_Перенос"):
    """Builds the reduced export in dst (absent or empty)."""
    res = Result(subsystem)
    _children_cache.clear()
    if not os.path.isfile(native(src, "Configuration.xml")):
        raise BuildError("Нет Configuration.xml в " + src)
    if os.path.exists(long_path(dst)) and os.listdir(long_path(dst)):
        raise BuildError("Каталог результата не пуст: " + dst)
    chosen = set()
    for o in objects:
        kind, name = split_key(o)
        if kind in ("Configuration", "Language"):
            raise BuildError(o + ": корень и языки переносятся всегда, их не выбирают.")
        if not name or "." in name or kind not in TYPE_FOLDERS:
            raise BuildError(o + ": ожидается Вид.Имя верхнего уровня (Catalog.Номенклатура).")
        if not exists(src, o):
            raise BuildError("Нет объекта " + o + " в выгрузке.")
        if o not in chosen:
            chosen.add(o)
            res.selected.append(o)
    if not res.selected:
        raise BuildError("Не выбрано ни одного объекта.")
    if exists(src, key_of("Subsystem", subsystem)):
        raise BuildError("В выгрузке уже есть подсистема " + subsystem + ".")

    dirty_heap, dirty = [], set()

    def mark(key):
        if key not in dirty:
            dirty.add(key)
            heapq.heappush(dirty_heap, key)

    exists_cache = {}

    below_cache = {}

    def below(key):
        v = below_cache.get(key)
        if v is None:
            v = below_cache[key] = files_below(src, key)
        return v

    def present_in_src(key):
        v = exists_cache.get(key)
        if v is None:
            v = exists_cache[key] = exists(src, key)
        return v

    def note(r, owner):
        """A reference found in owner's text: a stub or a member of one."""
        key = key_of(r.kind, r.name)
        if key in chosen or r.kind == "Language" or not present_in_src(key):
            return
        s = res.stubs.get(key)
        if s is None:
            s = res.stubs[key] = Stub()
            s.reason = owner
            mark(key)
        if r.member and not is_standard_member(r.member) and (r.member, r.member_name) not in s.members:
            s.members.add((r.member, r.member_name))
            mark(key)
        if r.predefined and not s.predefined:
            s.predefined = True
            mark(key)
        if r.member == "StandardCommand" and r.member_name == "CreateBasedOn" and not s.based_on:
            s.based_on = True
            mark(key)
        if r.member == "StandardCommand" and r.member_name == "OpenByValue" and not s.by_value:
            s.by_value = True
            mark(key)
        if r.member == "StandardCommand" and r.member_name == "Open" and r.kind in ("Report", "DataProcessor"):
            # A stub opens by its default form or, a report, by its main schema.
            text = descriptor(key)
            obj = object_element(text)
            props = find(children(text, obj.inner, obj.inner_end), "Properties") if obj else None
            for tag in OPEN_PROPERTIES:
                v = find(children(text, props.inner, props.inner_end), tag) if props else None
                for o in scan(text[v.inner:v.inner_end]) if v else []:
                    if key_of(o.kind, o.name) == key and o.member and (o.member, o.member_name) not in s.members:
                        s.members.add((o.member, o.member_name))
                        mark(key)

    descriptors = {}

    def descriptor(key):
        t = descriptors.get(key)
        if t is None:
            t = descriptors[key] = read_file(native(src, descriptor_rel(key)))
        return t

    index = {}

    def members(key):
        m = index.get(key)
        if m is None:
            m = {}
            text = descriptor(key)
            obj = object_element(text)
            if obj:
                c = find(children(text, obj.inner, obj.inner_end), "ChildObjects")
                if c:
                    m = index_members(text, c)
            index[key] = m
        return m

    def defined_types(key):
        text = descriptor(key)
        obj = object_element(text)
        return type_keys(text, obj) if obj else set()

    folder_names = {}

    def canonical(key):
        """The object as the export names it: the query language ignores case, and so
        does the file system of Windows, so the folder is listed."""
        kind, name = split_key(key)
        folder = TYPE_FOLDERS.get(kind)
        if not folder:
            return key
        names = folder_names.get(folder)
        if names is None:
            names = folder_names[folder] = {}
            for e in _listing(native(src, folder)):
                if e.name.endswith(".xml") and e.is_file():
                    names.setdefault(fold(e.name[:-4]), e.name[:-4])
        real = names.get(fold(name))
        return key_of(kind, real) if real else key

    common = None

    def common_attribute(field, key):
        """A common attribute named `field` that the object `key` has: its name, or ""."""
        nonlocal common
        if common is None:
            common = {}
            for e in _listing(native(src, "CommonAttributes")):
                if not e.name.endswith(".xml"):
                    continue
                text = read_file(e.path)
                obj = object_element(text)
                props = find(children(text, obj.inner, obj.inner_end), "Properties") if obj else None
                if not props:
                    continue
                parts = children(text, props.inner, props.inner_end)
                auto = find(parts, "AutoUse")
                uses = {}
                content = find(parts, "Content")
                for item in children(text, content.inner, content.inner_end) if content else []:
                    kids = children(text, item.inner, item.inner_end)
                    md, use = find(kids, "xr:Metadata"), find(kids, "xr:Use")
                    if md and use:
                        uses[text[md.inner:md.inner_end]] = text[use.inner:use.inner_end]
                common.setdefault(fold(e.name[:-4]), (e.name[:-4], text[auto.inner:auto.inner_end] if auto else "", uses))
        ca = common.get(fold(field))
        if not ca:
            return ""
        use = ca[2].get(key, "Auto")
        return ca[0] if use == "Use" or (use != "DontUse" and ca[1] == "Use") else ""

    def find_member(mm, name):
        """A member by name, the case of the query aside: (its name, Member) or (name, None)."""
        m = mm.get(name)
        if m is not None:
            return name, m
        f = fold(name)
        for k in sorted(mm):
            if fold(k) == f:
                return k, mm[k]
        return name, None

    registrars = None

    def registrars_of(key):
        """The documents of the export whose RegisterRecords name the register."""
        nonlocal registrars
        if registrars is None:
            registrars = {}
            for e in _listing(native(src, "Documents")):
                if not e.name.endswith(".xml") or not e.is_file():
                    continue
                text = read_file(e.path)
                a, b = text.find("<RegisterRecords>"), text.find("</RegisterRecords>")
                if a < 0 or b < 0:
                    continue
                for r in scan(text[a:b]):
                    registrars.setdefault(key_of(r.kind, r.name), []).append(key_of("Document", e.name[:-4]))
        return registrars.get(key, [])

    def listed(key, tag):
        """The objects a property of the descriptor names, in order: Owners, RegisteredDocuments, Content."""
        text = descriptor(key)
        obj = object_element(text)
        props = find(children(text, obj.inner, obj.inner_end), "Properties") if obj else None
        o = find(children(text, props.inner, props.inner_end), tag) if props else None
        out = []
        for r in scan(text[o.inner:o.inner_end]) if o else []:
            if key_of(r.kind, r.name) not in out:
                out.append(key_of(r.kind, r.name))
        return out

    def owners(key):
        """The owners of a catalog: its Владелец goes to them."""
        return set(listed(key, "Owners"))

    def having(candidates, field):
        """Of the objects a composite field may hold, those that have the next field: the ones
        already in the CF, else the first; a standard field (Дата) needs none of them."""
        with_it = [d for d in candidates if present_in_src(canonical(d)) and find_member(members(canonical(d)), field)[1] is not None]
        return set([d for d in with_it if d in chosen or d in res.stubs] or with_it[:1])

    def register_member(mm, field):
        """A field of a virtual table (КоличествоОстаток, СчетДт): the member it is of, or (field, None)."""
        f = fold(field)
        tries = [f[:-2]] if f.endswith(tuple(fold(s) for s in SIDE_SUFFIXES)) else []
        for t in [f] + tries:
            for suffix in RESOURCE_SUFFIXES:
                s = fold(suffix)
                if t.endswith(s) and len(t) > len(s):
                    tries.append(t[:-len(s)])
                    break
        for t in tries:
            real, m = find_member(mm, field[:len(t)])
            if m is not None:
                return real, m
        return field, None

    def walk(types, seg, i, owner, depth):
        """Объект.Счёт.Валюта: the stub of the account's type keeps Валюта, and so on down
        the path; a tabular section is walked by its columns. Ссылка goes back to the
        object, from a tabular section too (Т.Ссылка.Сотрудник); a field the object
        does not have may be a resource of a virtual table, the recorder of a register
        or a common attribute of it."""
        if i >= len(seg) or depth > 8:
            return
        for t0 in sorted(types):
            if t0 == CONSTANTS_SET:  # НаборКонстант.Валюта.Код
                ck = canonical(key_of("Constant", seg[i]))
                if present_in_src(ck):
                    note(Ref("Constant", split_key(ck)[1]), owner)
                    walk(defined_types(ck), seg, i + 1, owner, depth + 1)
                continue
            keys = {t0}
            if split_key(t0)[0] == "DefinedType" and present_in_src(t0):
                keys = defined_types(t0)
            for key in sorted(keys):
                key = canonical(key)
                if not present_in_src(key):
                    continue
                kind, name = split_key(key)
                if seg[i] == ALL_FIELDS:
                    if i == 0:
                        for field in sorted(members(key)):
                            note(Ref(kind, name, "*", field), owner)
                    continue
                if seg[i] == PREDEFINED:
                    if i + 1 < len(seg):
                        note(Ref(kind, name, "", "", seg[i + 1]), owner)
                    continue
                field, m = find_member(members(key), seg[i])
                if m is None and kind in REGISTER_KINDS:
                    field, m = register_member(members(key), field)
                note(Ref(kind, name, "*", field), owner)
                if m is None:  # a member of that name first: a register may have a dimension Ссылка
                    if fold(field) in ("ссылка", "ref") and kind in ("DocumentJournal", "FilterCriterion"):
                        # Журнал.Ссылка.Сотрудник: a document of the journal, an object of the criterion's content, that has it
                        if i + 1 < len(seg):
                            walk(having(listed(key, "RegisteredDocuments" if kind == "DocumentJournal" else "Content"),
                                        seg[i + 1]), seg, i + 1, owner, depth + 1)
                        continue
                    if fold(field) in ("ссылка", "ref"):
                        walk({key}, seg, i + 1, owner, depth + 1)
                        continue
                    if kind in ("Catalog", "ChartOfCharacteristicTypes") and fold(field) in ("владелец", "owner"):
                        walk(owners(key), seg, i + 1, owner, depth + 1)  # Сертификат.Владелец.Номинал
                        continue
                    if kind in REGISTER_KINDS and fold(field) in ("регистратор", "recorder"):
                        # Регистратор.Склад: a document writing the register that has Склад
                        if i + 1 < len(seg):
                            walk(having(registrars_of(key), seg[i + 1]), seg, i + 1, owner, depth + 1)
                        continue
                    ca = common_attribute(field, key)
                    if ca:
                        ca_key = key_of("CommonAttribute", ca)
                        note(Ref("CommonAttribute", ca), owner)
                        walk(defined_types(ca_key), seg, i + 1, owner, depth + 1)
                    continue
                j = i + 1
                while m is not None and m.tag == "TabularSection" and j < len(seg):
                    column, c = find_member(m.columns, seg[j])
                    if c is None and fold(column) in ("ссылка", "ref"):
                        walk({key}, seg, j + 1, owner, depth + 1)
                        m = None
                        break
                    m = c
                    j += 1
                if m is not None and j < len(seg):
                    walk(m.types, seg, j, owner, depth + 1)

    def scan_file(path, owner):
        if path.endswith(".bsl"):
            for key, p in module_values(read_file(path)):
                walk({key}, p, 0, owner, 0) if p else note(Ref(*split_key(canonical(key))), owner)
            return
        if not path.endswith(".xml"):
            return
        text = read_file(path)
        for r in scan(text):
            note(r, owner)
        if os.path.basename(path) == "Form.xml":
            for types, rest in form_paths(text):
                if not rest:
                    for key in sorted(canonical(t) for t in types):
                        kind, name = split_key(key)
                        note(Ref(kind, name), owner)
                else:
                    walk(types, rest, 0, owner, 0)

    for key in res.selected:
        for rel in below(key):
            scan_file(native(src, rel), key)

    built = {}  # stub → (descriptor, kept files)

    def included():
        return chosen | set(res.stubs)

    def closure():
        present = included()
        while dirty_heap:
            key = heapq.heappop(dirty_heap)
            dirty.discard(key)
            if len(present) != len(chosen) + len(res.stubs):
                present = included()
            keep = []
            text = stub_descriptor(descriptor(key), key, res.stubs[key], present, keep)
            kind, name = split_key(key)
            base = TYPE_FOLDERS[kind] + "/" + name + "/"
            files = []
            for rel in below(key):
                if rel.endswith(KEPT_MODULES):
                    continue
                for k in keep:
                    if rel == base + k or (k.endswith("/") and rel.startswith(base + k)):
                        files.append(rel)
                        break
            built[key] = (text, files, keep)
            for r in scan(text):  # its own members too
                note(r, key)
            for rel in files:
                scan_file(native(src, rel), key)

    # A register written by documents needs one of them in the CF: a chosen or stub document
    # whose RegisterRecords names it, else the first such document of the export as a stub.
    # Lists of stubs keep the items naming objects of the CF, so every pass rebuilds all
    # stubs until nothing new comes.
    def needs_registrar(key):
        kind = split_key(key)[0]
        if kind in ("AccumulationRegister", "AccountingRegister", "CalculationRegister"):
            return True
        return kind == "InformationRegister" and "<WriteMode>RecorderSubordinate</WriteMode>" in descriptor(key)

    before = -1
    while before != len(res.stubs):
        before = len(res.stubs)
        for key in sorted(res.stubs):
            mark(key)
        closure()
        for key in sorted(included()):
            if not needs_registrar(key):
                continue  # a chosen register as well as a stub
            docs = registrars_of(key)
            if docs and not any(d in chosen or d in res.stubs for d in docs):
                note(Ref("Document", split_key(docs[0])[1]), key)

    # Write: chosen objects whole, stubs, languages, root, subsystem.
    def put(rel, text):
        write_file(native(dst, rel), text)
        res.files.append(rel)

    def copy(rel):
        os.makedirs(os.path.dirname(native(dst, rel)), exist_ok=True)
        shutil.copyfile(native(src, rel), native(dst, rel))
        res.files.append(rel)

    for key in res.selected:
        for rel in below(key):
            copy(rel)
    for key in sorted(built):
        text, files, keep = built[key]
        put(descriptor_rel(key), text)
        for rel in files:
            copy(rel)
        kind, name = split_key(key)
        base = TYPE_FOLDERS[kind] + "/" + name + "/"
        props = [m for m in STUB_MODULES if has_text(native(src, base + "Ext/" + m + ".bsl"))]
        if kind == "FunctionalOption" and content_of(descriptor(key)) != content_of(text):
            props.append("Content")
        if props:
            res.rules[key] = props
        for k in keep:
            if k.startswith("Commands/") and has_text(native(src, base + k + "Ext/CommandModule.bsl")):
                res.rules[key + ".Command." + k[9:-1]] = ["CommandModule"]
            elif k.startswith("Forms/") and k.endswith(".xml") and has_text(native(src, base + k[:-4] + "/Ext/Form/Module.bsl")):
                res.rules[key + ".Form." + k[6:-4]] = ["Form"]

    cfg = read_file(native(src, "Configuration.xml"))
    obj = object_element(cfg)
    if not obj or obj.tag != "Configuration":
        raise BuildError("Configuration.xml: нет элемента Configuration.")
    res.configuration = member_name(cfg, obj)
    kept = included()
    root = [cfg[:obj.inner]]
    pos = obj.inner
    sub_xml = "<Subsystem>" + escape(subsystem) + "</Subsystem>"
    for s in children(cfg, obj.inner, obj.inner_end):
        root.append(cfg[pos:s.open])
        if s.tag == "Properties":
            root.append(clean_properties(cfg, s, "Configuration", "Language"))
        elif s.tag == "ChildObjects":
            body = []
            last = s.inner
            placed = False
            indent_before = ""
            for m in children(cfg, s.inner, s.inner_end):
                name = cfg[m.inner:m.inner_end]
                gap = cfg[last:m.open]
                last = m.end
                if not placed and m.tag != "Language" and (m.tag != "Subsystem" or name > subsystem):
                    body.append(gap + sub_xml)
                    placed = True
                if m.tag == "Language" or key_of(m.tag, name) in kept:
                    body.append(gap + cfg[m.open:m.end])
                if m.tag == "Language" and os.path.isfile(native(src, "Languages/" + name + ".xml")):
                    copy("Languages/" + name + ".xml")
                indent_before = gap
            if not placed:
                body.append(indent_before + sub_xml)
            root.append("<ChildObjects>" + "".join(body) + cfg[last:s.inner_end] + "</ChildObjects>")
        else:
            root.append(cfg[s.open:s.end])
        pos = s.end
    root.append(cfg[pos:])
    put("Configuration.xml", "".join(root))

    uuid_at = cfg.find('uuid="', obj.open)
    cfg_uuid = "" if uuid_at < 0 else cfg[uuid_at + 6:uuid_at + 42]
    items = "".join('\t\t\t\t<xr:Item xsi:type="xr:MDObjectRef">' + escape(k) + "</xr:Item>\r\n" for k in res.selected)
    put("Subsystems/" + subsystem + ".xml", cfg[:obj.open] +
        '<Subsystem uuid="' + stable_uuid(cfg_uuid + "/partial-cf/" + subsystem) + '">\r\n'
        "\t\t<Properties>\r\n\t\t\t<Name>" + escape(subsystem) + "</Name>\r\n\t\t\t<Synonym/>\r\n\t\t\t<Comment/>\r\n"
        "\t\t\t<IncludeHelpInContents>false</IncludeHelpInContents>\r\n\t\t\t<IncludeInCommandInterface>false</IncludeInCommandInterface>\r\n"
        "\t\t\t<UseOneCommand>false</UseOneCommand>\r\n\t\t\t<Explanation/>\r\n\t\t\t<Picture/>\r\n"
        "\t\t\t<Content>\r\n" + items + "\t\t\t</Content>\r\n\t\t</Properties>\r\n\t\t<ChildObjects/>\r\n\t</Subsystem>\r\n</MetaDataObject>")
    return res


def merge_settings(res):
    """/MergeCfg settings: the chosen objects from the file; the root and the transfer
    subsystem not merged, the stubs merged with the base first. Left out, the root is
    merged all the same (8.3.27, unrelated configurations: the base lost its
    Ext/ClientApplicationInterface.xml), and a stub overwrote its object in a reported
    base (issue 1); with DoNotMerge the root still takes new objects. A stub with
    DoNotMerge fails a large base: the owners, the types of a chart of characteristic
    types or the chart of an accounting register naming another stub are "unresolvable
    references"; merged with the base first, a stub changes nothing in it (a full dump
    compared, 8.3.27) once its modules and the cut Content of a functional option are
    not merged (res.rules): merged, they reordered the base's Content, added an end of
    line to its module and the methods of the CF's command module to the base's."""
    x = ["﻿<?xml version=\"1.0\" encoding=\"UTF-8\"?>\r\n"
         "<Settings xmlns=\"http://v8.1c.ru/8.3/config/merge/settings\" xmlns:xs=\"http://www.w3.org/2001/XMLSchema\" "
         "xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" version=\"1.2\" platformVersion=\"8.3.11\">\r\n"
         "\t<Parameters>\r\n\t\t<ConfigurationsRelation>ConfigurationsNotRelated</ConfigurationsRelation>\r\n"
         "\t\t<AllowMainConfigurationObjectDeletion>false</AllowMainConfigurationObjectDeletion>\r\n\t</Parameters>\r\n\t<Objects>\r\n"]

    def obj(name, rule, props=()):
        x.append("\t\t<Object fullNameInSecondConfiguration=\"" + escape(name) + "\">\r\n\t\t\t<MergeRule>" + rule + "</MergeRule>\r\n")
        if props:
            x.append("\t\t\t<Properties>\r\n")
            for p in props:
                x.append("\t\t\t\t<Property name=\"" + p + "\">\r\n\t\t\t\t\t<MergeRule>DoNotMerge</MergeRule>\r\n\t\t\t\t</Property>\r\n")
            x.append("\t\t\t</Properties>\r\n")
        x.append("\t\t</Object>\r\n")

    if res.configuration:
        obj("Configuration." + res.configuration, "DoNotMerge")
    for key in res.selected:
        if key in res.patched:
            x.extend(res.patched[key])
        else:
            obj(key, "GetFromSecondConfiguration")
    for key in sorted(res.stubs):
        obj(key, "MergePrioritizingMainConfiguration", res.rules.get(key, ()))
    for key in sorted(k for k in res.rules if k not in res.stubs):  # a command or a form a stub keeps
        obj(key, "MergePrioritizingMainConfiguration", res.rules[key])
    obj("Subsystem." + res.subsystem, "DoNotMerge")
    return "".join(x) + "\t</Objects>\r\n</Settings>\r\n"


# --- Changes (git) ----------------------------------------------------------------------

def parse_name_status(lines):
    """git diff --name-status lines → [(added|modified|deleted, path with '/')]."""
    out = []
    for raw in lines:
        line = raw.rstrip("\r\n")
        tab = line.find("\t")
        if tab <= 0:
            continue
        status = line[0]
        rest, second = line[tab + 1:], ""
        tab2 = rest.find("\t")
        if tab2 >= 0:
            rest, second = rest[:tab2], rest[tab2 + 1:]
        if status == "R":
            out += [("deleted", rest), ("added", second)]
        elif status == "C":
            out.append(("added", second or rest))
        elif status == "D":
            out.append(("deleted", rest))
        elif status == "A":
            out.append(("added", rest))
        else:
            out.append(("modified", rest))
    return out


def owner_xml(rel):
    """Catalogs/X/Forms/F/Ext/Form.xml → Catalogs/X.xml; a root file is its own."""
    path = rel.replace("\\", "/")
    while path.startswith("./"):
        path = path[2:]
    first = path.find("/")
    if first < 0:
        return path
    if path[:first].lower() == "ext":
        return "Configuration.xml"
    second = path.find("/", first + 1)
    return path if second < 0 else path[:second] + ".xml"


def objects_of_changes(changes, exists_rel):
    """The owners of changed files: objects, root files apart, deleted objects."""
    objects, root, deleted = [], [], []
    by_folder = {f: k for k, f in TYPE_FOLDERS.items()}
    for _, path in changes:
        rel = owner_xml(path)
        if os.path.basename(path.replace("\\", "/")).lower() == "configdumpinfo.xml":
            continue
        if rel == "Configuration.xml" or "/" not in rel:
            if rel not in root:
                root.append(rel)
            continue
        slash = rel.find("/")
        folder, name = rel[:slash], rel[slash + 1:-4]
        kind = by_folder.get(folder, "")
        if not kind or kind == "Language":
            if rel not in root:
                root.append(rel)
            continue
        key = key_of(kind, name)
        if not exists_rel(rel):
            if key not in deleted:
                deleted.append(key)
            continue
        if key not in objects:
            objects.append(key)
    return objects, root, deleted


def git(export, *args):
    p = subprocess.run(["git", "-C", export, "-c", "core.quotepath=off", *args], capture_output=True)
    return p.returncode, p.stdout.decode("utf-8", "surrogateescape"), p.stderr.decode("utf-8", "replace")


def git_changed_files(export, since, until=""):
    """[(added|modified|deleted, path)] from since to until, or to the working tree with
    the untracked files when until is empty."""
    for rev in (since, until):
        if rev and git(export, "rev-parse", "--verify", "--quiet", rev + "^{commit}")[0] != 0:
            raise BuildError("Ревизия git '" + rev + "' не найдена в " + export + ".")
    code, diff, err = git(export, "diff", "--name-status", "--relative", since, *([until] if until else []), "--", ".")
    if code != 0:
        raise BuildError("git diff: " + err.strip()[:1000])
    lines = diff.splitlines()
    if not until:
        code, untracked, _ = git(export, "ls-files", "--others", "--exclude-standard")
        if code == 0:
            lines += ["A\t" + u for u in untracked.splitlines() if u]
    return parse_name_status(lines)


def git_changes(export, since, until=""):
    changes = git_changed_files(export, since, until)
    exists_rel = (lambda rel: git(export, "cat-file", "-e", until + ":./" + rel)[0] == 0) if until else \
        (lambda rel: os.path.isfile(native(export, rel)))
    return objects_of_changes(changes, exists_rel)


# --- Module patches -------------------------------------------------------------------

MODULE_PROPS = ("ObjectModule", "ManagerModule", "RecordSetModule", "ValueManagerModule", "CommandModule", "Module")
METHOD_START = re.compile(r"[ \t]*(?:(?:Асинх|Async)[ \t]+)?(?:Процедура|Функция|Procedure|Function)[ \t]+([^\s(]+)[ \t]*\(", re.I)
METHOD_END = re.compile(r"[ \t]*(?:КонецПроцедуры|КонецФункции|EndProcedure|EndFunction)(?![\wА-Яа-яЁё])", re.I)


def module_of(rel):
    """A module file of the export → (object, settings name, property); None for another file.
    Catalogs/X/Ext/ObjectModule.bsl → (Catalog.X, Catalog.X, ObjectModule); a form module →
    (Catalog.X, Catalog.X.Form.F, Form); a command module → (Catalog.X, Catalog.X.Command.C,
    CommandModule). The property names are those of the /MergeCfg settings (8.3.27)."""
    p = rel.replace("\\", "/").split("/")
    kind = {f: k for k, f in TYPE_FOLDERS.items()}.get(p[0])
    if not kind or kind == "Language" or len(p) < 4:
        return None
    key = key_of(kind, p[1])
    if len(p) == 4 and p[2] == "Ext" and p[3].endswith(".bsl") and p[3][:-4] in MODULE_PROPS:
        return key, key, p[3][:-4]
    if kind == "CommonForm" and p[2:] == ["Ext", "Form", "Module.bsl"]:
        return key, key, "Form"
    if len(p) == 7 and p[2] == "Forms" and p[4:] == ["Ext", "Form", "Module.bsl"]:
        return key, key + ".Form." + p[3], "Form"
    if len(p) == 6 and p[2] == "Commands" and p[4:] == ["Ext", "CommandModule.bsl"]:
        return key, key + ".Command." + p[3], "CommandModule"
    return None


def parse_method(spec):
    """CommonModule.М.Метод, Document.Д.ObjectModule.Метод, Document.Д.Form.Ф.Метод,
    Document.Д.Command.К.Метод, CommonForm.Ф.Метод, CommonCommand.К.Метод →
    (settings name, property, method)."""
    p = spec.split(".")
    if len(p) >= 3 and p[0] in TYPE_FOLDERS and all(p):
        key = key_of(p[0], p[1])
        common = {"CommonModule": "Module", "CommonForm": "Form", "CommonCommand": "CommandModule"}
        if len(p) == 3 and p[0] in common:
            return key, common[p[0]], p[2]
        if len(p) == 4 and p[2] in MODULE_PROPS:
            return key, p[2], p[3]
        if len(p) == 5 and p[2] in ("Form", "Command"):
            return key + "." + p[2] + "." + p[3], "Form" if p[2] == "Form" else "CommandModule", p[4]
    raise BuildError(spec + ": ожидается CommonModule.Модуль.Метод, Document.Документ.ObjectModule.Метод, "
                     "Document.Документ.Form.Форма.Метод и т. п.")


def module_text(text):
    """A module as compared and patched: no BOM, LF line ends."""
    return (text or "").lstrip("﻿").replace("\r\n", "\n")


def method_owners(lines):
    """For every line of a module the method it belongs to — its header, body and the
    comments and compile directives right above it — None outside methods."""
    owner = [None] * len(lines)
    i = 0
    while i < len(lines):
        m = METHOD_START.match(lines[i])
        if not m:
            i += 1
            continue
        j = i
        while j < len(lines) and not METHOD_END.match(lines[j]):
            j += 1
        a = i
        while a > 0 and owner[a - 1] is None and lines[a - 1].lstrip().startswith(("//", "&")):
            a -= 1
        for k in range(a, min(j, len(lines) - 1) + 1):
            owner[k] = m.group(1).lower()
        i = j + 1
    return owner


def keep_methods(target, merged, names):
    """target with the changes of merged inside the methods names (lower case) only →
    (text, the other methods changed, '' for a change outside methods)."""
    a, b = target.split("\n"), merged.split("\n")
    oa, ob = method_owners(a), method_owners(b)
    out, skipped = [], set()
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == "equal":
            out += a[i1:i2]
            continue
        # an empty line between methods goes with the change it is part of
        owners = {o or "" for line, o in zip(a[i1:i2] + b[j1:j2], oa[i1:i2] + ob[j1:j2]) if line.strip()}
        if owners and owners <= names:
            out += b[j1:j2]
        else:
            out += a[i1:i2]
            skipped |= owners - names
    return "\n".join(out), sorted(skipped)


def unified_patch(a, b):
    """The unidiff /MergeCfg applies to the base module (LF; the Designer refuses a hunk whose
    context differs, CRLF in a patch doubles the line ends)."""
    out = []
    for line in difflib.unified_diff(a.splitlines(True), b.splitlines(True), "a/Module", "b/Module"):
        out.append(line if line.endswith("\n") else line + "\n\\ No newline at end of file\n")
    return "".join(out)


def merge3(ours, base, theirs, tmp):
    """git merge-file: the changes from base to theirs put onto ours → (text, conflicts)."""
    paths = []
    for n, t in (("ours", ours), ("base", base), ("theirs", theirs)):
        p = os.path.join(tmp, "merge-" + n)
        with open(p, "wb") as f:
            f.write(t.encode("utf-8", "surrogateescape"))
        paths.append(p)
    r = subprocess.run(["git", "merge-file", "-p", "-L", "база", "-L", "было", "-L", "задача"] + paths, capture_output=True)
    if r.returncode < 0 or r.returncode > 127:
        raise BuildError("git merge-file: " + r.stderr.decode("utf-8", "replace").strip()[:500])
    return r.stdout.decode("utf-8", "surrogateescape"), r.returncode


class Patch:
    __slots__ = ("rel", "entry", "prop", "base", "text")

    def __init__(self, rel, entry, prop, base, text):
        self.rel, self.entry, self.prop, self.base, self.text = rel, entry, prop, base, text


def plan_patches(export, since, until, target, changes, methods, tmp, report):
    """The objects changed in modules only → {object: [Patch]}; the rest goes whole.

    The task's change of a module is since → until (the working tree without until). The
    patch is made on the module of the base: the target export's when given (the change
    merged onto it with git merge-file; a conflict stops the build), else the module as at
    since. With methods only the changes inside those methods go."""
    chosen = {}
    for spec in methods:
        entry, prop, name = parse_method(spec)
        chosen.setdefault((entry, prop), set()).add(name.lower())
    by_object = {}
    for status, path in changes:
        owner = owner_xml(path)
        slash = owner.find("/")
        kind = {f: k for k, f in TYPE_FOLDERS.items()}.get(owner[:slash]) if slash > 0 else None
        if kind and kind != "Language":
            by_object.setdefault(key_of(kind, owner[slash + 1:-4]), []).append((status, path))
    patches, whole, unchanged, conflicts, skipped = {}, [], [], [], []
    for key in sorted(by_object):
        files = by_object[key]
        other = [p for s, p in files if module_of(p) is None or s == "deleted"]
        if other:
            whole.append({"object": key, "reason": "изменён не только модуль: " + other[0]})
            continue
        for status, rel in files:
            _, entry, prop = module_of(rel)
            names = chosen.get((entry, prop))
            if methods and names is None:
                skipped.append({"module": rel, "reason": "методы модуля не выбраны"})
                continue
            old = module_text(git(export, "show", since + ":./" + rel)[1]) if status != "added" else ""
            new = module_text(git(export, "show", until + ":./" + rel)[1] if until else read_file(native(export, rel)))
            base = module_text(read_file(native(target, rel))) if target and os.path.isfile(native(target, rel)) else \
                ("" if target else old)
            merged, n = (new, 0) if base == old else merge3(base, old, new, tmp)
            if n:
                conflicts.append({"module": rel, "conflicts": n, "text": merged})
                continue
            if names is not None:
                merged, other_methods = keep_methods(base, merged, names)
                if other_methods:
                    skipped.append({"module": rel, "reason": "изменения вне выбранных методов не переносятся",
                                    "methods": [m or "(вне методов)" for m in other_methods]})
            if merged == base:
                unchanged.append(rel)
                continue
            patches.setdefault(key, []).append(Patch(rel, entry, prop, base, merged))
    for (entry, prop), names in sorted(chosen.items()):
        if not any(p.entry == entry and p.prop == prop for ps in patches.values() for p in ps):
            skipped.append({"module": entry + "." + prop, "reason": "нет изменений в выбранных методах"})
    for k, v in (("patched_whole", whole), ("patch_unchanged", unchanged), ("patch_skipped", skipped)):
        if v:
            report[k] = v
    return patches, [w["object"] for w in whole], conflicts


def apply_patches(res, dst, target, export, since, patches):
    """The CF and the settings of the objects moved by patches. Merged with the base first
    (8.3.27): a patched module gets its Patch; a module of the object not patched stays out
    of the CF and gets DoNotMerge when the base has it, else the base takes its methods;
    the forms, commands and templates not patched are not merged; a patched form keeps the
    base's elements, only its module patched."""
    for key, plist in patches.items():
        kind, name = split_key(key)
        base_dir = TYPE_FOLDERS[kind] + "/" + name + "/"

        def base_has(rel):
            if target:
                return has_text(native(target, rel))
            code, text, _ = git(export, "show", since + ":./" + rel)
            return code == 0 and bool(module_text(text).strip(" \t\r\n\x0b\x0c"))

        own = {}
        for rel in list(res.files):
            m = module_of(rel)
            if m and m[0] == key and m[1] == key:
                own[m[2]] = rel
        patched = {(p.entry, p.prop): p for p in plist}
        for p in plist:
            write_file(native(dst, p.rel), "﻿" + p.text.replace("\n", "\r\n"))
            if p.rel not in res.files:
                res.files.append(p.rel)

        def patch_xml(p, indent):
            return indent + "<Module>\r\n" + indent + "\t<Patch>" + escape(unified_patch(p.base, p.text)) + "</Patch>\r\n" + indent + "</Module>\r\n"

        x = ["\t\t<Object fullNameInSecondConfiguration=\"" + escape(key) + "\">\r\n\t\t\t<MergeRule>MergePrioritizingMainConfiguration</MergeRule>\r\n"]
        props = []
        for prop in MODULE_PROPS + ("Form",):
            p = patched.get((key, prop))
            if p is not None:
                body = patch_xml(p, "\t\t\t\t\t")
                if prop == "Form":
                    body = ("\t\t\t\t\t<FormModule>\r\n\t\t\t\t\t\t<MergeRule>MergePrioritizingSecondConfiguration</MergeRule>\r\n"
                            + patch_xml(p, "\t\t\t\t\t\t") + "\t\t\t\t\t</FormModule>\r\n")
                props.append("\t\t\t\t<Property name=\"" + prop + "\">\r\n" + body + "\t\t\t\t</Property>\r\n")
            elif prop in own:
                rel = own[prop]
                os.remove(native(dst, rel))
                res.files.remove(rel)
                if base_has(rel):
                    props.append("\t\t\t\t<Property name=\"" + prop + "\">\r\n\t\t\t\t\t<MergeRule>DoNotMerge</MergeRule>\r\n\t\t\t\t</Property>\r\n")
        if props:
            x += ["\t\t\t<Properties>\r\n"] + props + ["\t\t\t</Properties>\r\n"]
        x.append("\t\t</Object>\r\n")
        children = set()
        for rel in res.files:
            if rel.startswith(base_dir):
                part = rel[len(base_dir):].split("/")
                if len(part) >= 2 and part[0] in ("Forms", "Commands", "Templates"):
                    child = part[1][:-4] if part[1].endswith(".xml") and len(part) == 2 else part[1]
                    children.add(({"Forms": "Form", "Commands": "Command", "Templates": "Template"}[part[0]], child))
        for tag, child in sorted(children):
            entry = key + "." + tag + "." + child
            p = patched.get((entry, "Form" if tag == "Form" else "CommandModule"))
            if p is None:
                x.append("\t\t<Object fullNameInSecondConfiguration=\"" + escape(entry) + "\">\r\n\t\t\t<MergeRule>DoNotMerge</MergeRule>\r\n\t\t</Object>\r\n")
                continue
            body = patch_xml(p, "\t\t\t\t\t")
            if tag == "Form":
                body = ("\t\t\t\t\t<FormModule>\r\n\t\t\t\t\t\t<MergeRule>MergePrioritizingSecondConfiguration</MergeRule>\r\n"
                        + patch_xml(p, "\t\t\t\t\t\t") + "\t\t\t\t\t</FormModule>\r\n")
            x.append("\t\t<Object fullNameInSecondConfiguration=\"" + escape(entry) + "\">\r\n\t\t\t<MergeRule>MergePrioritizingMainConfiguration</MergeRule>\r\n"
                     "\t\t\t<Properties>\r\n\t\t\t\t<Property name=\"" + p.prop + "\">\r\n" + body + "\t\t\t\t</Property>\r\n\t\t\t</Properties>\r\n\t\t</Object>\r\n")
        res.patched[key] = x


# --- ibcmd ----------------------------------------------------------------------

def find_ibcmd(platform):
    found = []
    if os.name == "nt":
        roots = [os.path.join(os.environ.get(v, ""), "1cv8") for v in ("ProgramFiles", "ProgramFiles(x86)") if os.environ.get(v)]
        rel = os.path.join("bin", "ibcmd.exe")
    else:
        roots = ["/opt/1cv8/x86_64", "/opt/1cv8/aarch64", "/opt/1cv8/e2kv4", "/opt/1C/v8.3/x86_64"]
        rel = "ibcmd"
    for r in roots:
        if not os.path.isdir(r):
            continue
        for e in os.scandir(r):
            if re.fullmatch(r"\d+(\.\d+){3}", e.name) and (not platform or e.name.startswith(platform)) \
                    and os.path.isfile(os.path.join(e.path, rel)):
                found.append((tuple(int(x) for x in e.name.split(".")), os.path.join(e.path, rel)))
    if not found and os.name != "nt" and shutil.which("ibcmd"):
        return shutil.which("ibcmd")
    return max(found)[1] if found else ""


def run_ibcmd(ibcmd, args, timeout):
    p = subprocess.run([ibcmd, *args], capture_output=True, timeout=timeout)
    text = (p.stdout + p.stderr).decode("utf-8", "replace")
    return p.returncode, [l for l in text.splitlines() if l.strip()]


# --- Command line ----------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description="Маленькая CF из выгрузки конфигурации 1С для «Сравнить, объединить».")
    ap.add_argument("--export", required=True, help="каталог выгрузки (или его Configuration.xml)")
    ap.add_argument("--out", help="файл CF; рядом пишется <имя>.merge-settings.xml")
    ap.add_argument("--objects", nargs="*", default=[], help="Вид.Имя верхнего уровня: Document.Заказ Catalog.Товары")
    ap.add_argument("--since", default="", help="ревизия git выгрузки: изменённые с неё и новые объекты")
    ap.add_argument("--until", default="", help="конец изменений задачи (ревизия git); без него — рабочее дерево")
    ap.add_argument("--patch", action="store_true",
                    help="объекты, у которых изменены только модули, переносить патчами модулей, а не целиком")
    ap.add_argument("--target", default="", help="выгрузка базы-получателя: патчи строятся на её модулях")
    ap.add_argument("--methods", nargs="*", default=[],
                    help="переносить изменения только этих методов: CommonModule.М.Метод, Document.Д.ObjectModule.Метод, "
                         "Document.Д.Form.Ф.Метод")
    ap.add_argument("--platform", default="", help="версия платформы для поиска ibcmd, например 8.3.27")
    ap.add_argument("--ibcmd", default="", help="путь к ibcmd")
    ap.add_argument("--source-only", default="", help="только урезанная выгрузка в этот каталог, без ibcmd")
    ap.add_argument("--settings", default="", help="путь настроек объединения (по умолчанию рядом с CF)")
    ap.add_argument("--keep", action="store_true", help="оставить временный каталог")
    ap.add_argument("--timeout", type=int, default=1800, help="предел ibcmd, секунд")
    a = ap.parse_args(argv)

    report = {"ok": False}

    def finish(code):
        sys.stdout.write(json.dumps(report, ensure_ascii=False, indent=1) + "\n")
        return code

    export = os.path.abspath(a.export)
    if os.path.basename(export).lower() == "configuration.xml":
        export = os.path.dirname(export)
    objects = [o for item in a.objects for o in re.split(r"[,\s]+", item) if o]
    if not a.out and not a.source_only:
        report["error"] = "Укажите --out (файл CF) или --source-only."
        return finish(2)
    if not objects and not a.since:
        report["error"] = "Укажите --objects и/или --since."
        return finish(2)
    methods = [m for item in a.methods for m in re.split(r"[,\s]+", item) if m]
    patch_mode = a.patch or bool(methods)
    if (patch_mode or a.until or a.target) and not a.since:
        report["error"] = "--patch, --methods, --until и --target работают вместе с --since."
        return finish(2)
    target = os.path.abspath(a.target) if a.target else ""
    if target and os.path.basename(target).lower() == "configuration.xml":
        target = os.path.dirname(target)
    if target and not os.path.isdir(target):
        report["error"] = "Нет каталога выгрузки базы " + target + "."
        return finish(2)
    ibcmd = ""
    if not a.source_only:
        ibcmd = a.ibcmd or find_ibcmd(a.platform)
        if not ibcmd:
            report["error"] = "Не найден ibcmd платформы " + (a.platform or "1С") + "; укажите --ibcmd."
            return finish(2)
    tmp = tempfile.mkdtemp(prefix="partial-cf-")
    try:
        out_cf = os.path.abspath(a.out) if a.out else ""
        settings = a.settings or (os.path.splitext(out_cf)[0] + ".merge-settings.xml" if out_cf else
                                  os.path.join(os.path.dirname(os.path.abspath(a.source_only)),
                                               os.path.basename(os.path.abspath(a.source_only)) + ".merge-settings.xml"))
        stem = settings[:-len(".merge-settings.xml")] if settings.endswith(".merge-settings.xml") else settings
        patches = {}
        if a.since:
            changes = git_changed_files(export, a.since, a.until)
            changed, root, deleted = git_changes(export, a.since, a.until)
            report["changed"] = changed
            if root:
                report["root_changed"] = root
            if deleted:
                report["deleted"] = deleted
            if patch_mode:
                explicit = set(objects)
                patches, whole, conflicts = plan_patches(export, a.since, a.until, target, changes, methods, tmp, report)
                if conflicts:
                    folder = stem + ".conflicts"
                    for c in conflicts:
                        write_file(native(folder, c["module"]), "﻿" + c.pop("text").replace("\n", "\r\n"))
                    report.update({"error": "Изменения задачи пересекаются с правками базы: разрешите конфликты вручную.",
                                   "conflicts": conflicts, "conflicts_folder": folder})
                    return finish(1)
                for key in explicit:
                    patches.pop(key, None)
                changed = [o for o in changed if o in patches or o in whole]
            objects += [o for o in changed if o not in objects]
        if not objects:
            report["error"] = "Нет изменённых объектов с " + a.since + "."
            return finish(1)
        source = os.path.abspath(a.source_only) if a.source_only else os.path.join(tmp, "src")
        started = time.time()
        res = build(export, source, objects)
        apply_patches(res, source, target, export, a.since, patches)
        if patches:
            report["patched"] = [{"object": k, "modules": [p.rel for p in v]} for k, v in sorted(patches.items())]
        write_file(settings, merge_settings(res))
        # Hundreds of stubs do not fit an answer: counts by kind, the first ones and the whole list in a file.
        stubs = [{"object": k, "referred_by": res.stubs[k].reason} for k in sorted(res.stubs)]
        stubs_file = (settings[:-len(".merge-settings.xml")] if settings.endswith(".merge-settings.xml") else settings) + ".stubs.json"
        write_file(stubs_file, json.dumps(stubs, ensure_ascii=False, indent=1))
        kinds = {}
        for k in sorted(res.stubs):
            kinds[k.split(".")[0]] = kinds.get(k.split(".")[0], 0) + 1
        report.update({
            "selected": res.selected, "stubs_total": len(res.stubs), "stubs_by_kind": kinds,
            "stubs": stubs[:30], "stubs_file": stubs_file,
            "files": len(res.files), "subsystem": res.subsystem, "merge_settings": settings,
            "build_seconds": round(time.time() - started, 1),
        })
        if a.source_only:
            report.update({"ok": True, "source": source})
            return finish(0)
        started = time.time()
        os.makedirs(os.path.dirname(out_cf), exist_ok=True)
        if os.path.exists(out_cf):
            os.remove(out_cf)
        db, data = os.path.join(tmp, "ib"), os.path.join(tmp, "data")
        code, log = run_ibcmd(ibcmd, ["infobase", "create", "--db-path=" + db, "--data=" + data], a.timeout)
        if code != 0:
            report.update({"error": "ibcmd infobase create завершился с кодом %d." % code, "ibcmd_log": log[-20:]})
            return finish(1)
        code, log = run_ibcmd(ibcmd, ["config", "import", "--db-path=" + db, "--data=" + data, "--out=" + out_cf, source], a.timeout)
        report.update({"ibcmd": ibcmd, "import_seconds": round(time.time() - started, 1)})
        if code != 0 or not os.path.isfile(out_cf):
            report.update({"error": "ibcmd config import завершился с кодом %d." % code,
                           "ibcmd_errors": [l for l in log if "ERROR" in l or "Ошибка" in l][:20] or log[-20:]})
            if a.keep:
                report["temp"] = tmp
            return finish(1)
        report.update({"ok": True, "cf": out_cf, "cf_size": os.path.getsize(out_cf)})
        if a.keep:
            report["temp"] = tmp
        return finish(0)
    except BuildError as e:
        report["error"] = str(e)
        return finish(1)
    except subprocess.TimeoutExpired:
        report["error"] = "ibcmd не уложился в %d с." % a.timeout
        return finish(1)
    finally:
        if not a.keep:
            shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
