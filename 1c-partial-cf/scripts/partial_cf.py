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
    "Константа": "Constant", "Последовательность": "Sequence",
}
VIRTUAL_TABLES = {"СрезПоследних", "СрезПервых", "Остатки", "Обороты", "ОстаткиИОбороты",
                  "ДвиженияССубконто", "ОборотыДтКт", "Субконто", "ДанныеГрафика", "Изменения", "SliceLast", "SliceFirst", "Balance",
                  "Turnovers", "BalanceAndTurnovers", "RecordsWithExtDimensions", "DrCrTurnovers", "ExtDimensions", "ScheduleData", "Changes"}
AS_WORDS = {"КАК", "как", "Как", "AS", "as", "As"}


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

def read_file(path):
    try:
        with open(path, "rb") as f:
            return f.read().decode("utf-8", "surrogateescape")
    except OSError:
        return ""


def write_file(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(text.encode("utf-8", "surrogateescape"))


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
    return os.path.join(src, *rel.split("/"))


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
    __slots__ = ("reason", "members", "predefined", "based_on")

    def __init__(self):
        self.reason = ""          # the object that refers to it first
        self.members = set()      # (keyword, name); keyword * for a name of a data path
        self.predefined = False
        self.based_on = False     # its CreateBasedOn command is used: BasedOn stays non-empty


def _indent_before(text, inner, inner_end):
    nl = text.rfind("\n", 0, inner_end + 1)
    return text[nl:inner_end] if nl >= 0 and nl > inner else ""


def clean_properties(text, props, self_key, keep_kind, present=frozenset(), based_on=False):
    """A property referring to another object, or to a non-standard member of its own,
    becomes empty; Name, Synonym, Comment, Type and the required ones stay. Of a list the
    items naming only objects of the CF stay."""
    kind = split_key(self_key)[0]

    def foreign(part):
        for r in scan(part):
            if keep_kind and r.kind == keep_kind:
                continue
            if key_of(r.kind, r.name) == self_key and (not r.member or is_standard_member(r.member)) and not r.predefined:
                continue
            return True
        return False

    out = [text[props.open:props.inner]]
    pos = props.inner
    for p in children(text, props.inner, props.inner_end):
        out.append(text[pos:p.open])
        keep_all = p.tag in ("Name", "Synonym", "Comment", "Type") or p.tag in REQUIRED_PROPERTIES.get(kind, ())
        if keep_all or not foreign(text[p.inner:p.inner_end]):
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
            out.append(clean_properties(text, s, key, "", present, stub.based_on))
        elif s.tag == "ChildObjects":
            kept = ""
            last = s.inner
            kids = children(text, s.inner, s.inner_end)
            names = [member_name(text, m) for m in kids]

            def wanted(i):
                return (kids[i].tag, names[i]) in stub.members or ("*", names[i]) in stub.members

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


def query_refs(query):
    """Sources of a dynamic list query (Справочник.Партнеры КАК П) and the fields read
    through them (П.Менеджер.Имя): (object, path); a tabular section source starts the path."""
    words = []  # dotted chains; strings, comments and parameters skipped
    n = len(query)
    i = 0
    while i < n:
        c = query[i]
        if c == '"':
            e = query.find('"', i + 1)
            i = n if e < 0 else e + 1
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
        words.append(seg)
        i = j

    def kind_word(w):
        if w in QUERY_KINDS:
            return QUERY_KINDS[w]
        return w if w in TYPE_FOLDERS and w != "Language" else ""

    out, alias = [], {}
    for k, seg in enumerate(words):
        kind = kind_word(seg[0]) if len(seg) >= 2 else ""
        if not kind:
            continue
        key = key_of(kind, seg[1])
        section = [seg[2]] if len(seg) >= 3 and seg[2] not in VIRTUAL_TABLES else []
        out.append((key, section))
        name = seg[-1]
        if k + 2 < len(words) and len(words[k + 1]) == 1 and words[k + 1][0] in AS_WORDS:
            name = words[k + 2][0]
        alias[name] = (key, section)
    for seg in words:
        if len(seg) < 2 or seg[0] not in alias:
            continue
        key, section = alias[seg[0]]
        out.append((key, section + seg[1:]))
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
    Items.Таблица.CurrentData.Колонка goes through the DataPath of the item."""
    out = []
    root = find(children(form, 0, len(form)), "Form")
    if not root:
        return out
    attrs = {}
    a = find(children(form, root.inner, root.inner_end), "Attributes")
    if a:
        for at in children(form, a.inner, a.inner_end):
            name = attribute_value(form, at.open, at.inner, "name")
            kids = children(form, at.inner, at.inner_end)
            types = set()
            t = find(kids, "Type")
            if t:
                types.update(key_of(r.kind, r.name) for r in scan(form[t.inner:t.inner_end]))
            settings = find(kids, "Settings")
            if settings:  # a dynamic list: its main table and query
                opts = children(form, settings.inner, settings.inner_end)
                main = find(opts, "MainTable")
                if main:
                    types.update(key_of(r.kind, r.name) for r in scan(form[main.inner:main.inner_end]))
                q = find(opts, "QueryText")
                if q:
                    for key, path in query_refs(xml_text(form[q.inner:q.inner_end])):
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
        self.files = []      # written, relative to the output


def build(src, dst, objects, subsystem="_Перенос"):
    """Builds the reduced export in dst (absent or empty)."""
    res = Result(subsystem)
    _children_cache.clear()
    if not os.path.isfile(os.path.join(src, "Configuration.xml")):
        raise BuildError("Нет Configuration.xml в " + src)
    if os.path.exists(dst) and os.listdir(dst):
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

    def walk(types, seg, i, owner, depth):
        """Объект.Счёт.Валюта: the stub of the account's type keeps Валюта, and so on down
        the path; a tabular section is walked by its columns."""
        if i >= len(seg) or depth > 8:
            return
        for t0 in sorted(types):
            keys = {t0}
            if split_key(t0)[0] == "DefinedType" and present_in_src(t0):
                keys = defined_types(t0)
            for key in sorted(keys):
                if not present_in_src(key):
                    continue
                kind, name = split_key(key)
                note(Ref(kind, name, "*", seg[i]), owner)
                m = members(key).get(seg[i])
                if m is None:
                    continue
                j = i + 1
                while m is not None and m.tag == "TabularSection" and j < len(seg):
                    m = m.columns.get(seg[j])
                    j += 1
                if m is not None and j < len(seg):
                    walk(m.types, seg, j, owner, depth + 1)

    def scan_file(path, owner):
        if not path.endswith(".xml"):
            return
        text = read_file(path)
        for r in scan(text):
            note(r, owner)
        if os.path.basename(path) == "Form.xml":
            for types, rest in form_paths(text):
                if not rest:
                    for key in sorted(types):
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
                for k in keep:
                    if rel == base + k or (k.endswith("/") and rel.startswith(base + k)):
                        files.append(rel)
                        break
            built[key] = (text, files)
            for r in scan(text):  # its own members too
                note(r, key)
            for rel in files:
                scan_file(native(src, rel), key)

    # A register written by documents needs one of them in the CF: a chosen or stub document
    # whose RegisterRecords names it, else the first such document of the export as a stub.
    # Lists of stubs keep the items naming objects of the CF, so every pass rebuilds all
    # stubs until nothing new comes.
    registrars = None

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
            if registrars is None:
                registrars = {}
                for e in _listing(os.path.join(src, "Documents")):
                    if not e.name.endswith(".xml") or not e.is_file():
                        continue
                    text = read_file(e.path)
                    a, b = text.find("<RegisterRecords>"), text.find("</RegisterRecords>")
                    if a < 0 or b < 0:
                        continue
                    for r in scan(text[a:b]):
                        registrars.setdefault(key_of(r.kind, r.name), []).append(key_of("Document", e.name[:-4]))
            docs = registrars.get(key, [])
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
        text, files = built[key]
        put(descriptor_rel(key), text)
        for rel in files:
            copy(rel)

    cfg = read_file(os.path.join(src, "Configuration.xml"))
    obj = object_element(cfg)
    if not obj or obj.tag != "Configuration":
        raise BuildError("Configuration.xml: нет элемента Configuration.")
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
    """/MergeCfg settings: the chosen objects from the file, the transfer subsystem not
    merged; stubs are left out, which keeps them out of the base."""
    x = ["﻿<?xml version=\"1.0\" encoding=\"UTF-8\"?>\r\n"
         "<Settings xmlns=\"http://v8.1c.ru/8.3/config/merge/settings\" xmlns:xs=\"http://www.w3.org/2001/XMLSchema\" "
         "xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" version=\"1.2\" platformVersion=\"8.3.11\">\r\n"
         "\t<Parameters>\r\n\t\t<ConfigurationsRelation>ConfigurationsNotRelated</ConfigurationsRelation>\r\n"
         "\t\t<AllowMainConfigurationObjectDeletion>false</AllowMainConfigurationObjectDeletion>\r\n\t</Parameters>\r\n\t<Objects>\r\n"]

    def obj(name, rule):
        x.append("\t\t<Object fullNameInSecondConfiguration=\"" + escape(name) + "\">\r\n\t\t\t<MergeRule>" + rule +
                 "</MergeRule>\r\n\t\t</Object>\r\n")

    for key in res.selected:
        obj(key, "GetFromSecondConfiguration")
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


def git_changes(export, since):
    def git(*args):
        p = subprocess.run(["git", "-C", export, "-c", "core.quotepath=off", *args], capture_output=True)
        return p.returncode, p.stdout.decode("utf-8", "surrogateescape"), p.stderr.decode("utf-8", "replace")

    code, _, _ = git("rev-parse", "--verify", "--quiet", since + "^{commit}")
    if code != 0:
        raise BuildError("Ревизия git '" + since + "' не найдена в " + export + ".")
    code, diff, err = git("diff", "--name-status", "--relative", since, "--", ".")
    if code != 0:
        raise BuildError("git diff: " + err.strip()[:1000])
    lines = diff.splitlines()
    code, untracked, _ = git("ls-files", "--others", "--exclude-standard")
    if code == 0:
        lines += ["A\t" + u for u in untracked.splitlines() if u]
    return objects_of_changes(parse_name_status(lines), lambda rel: os.path.isfile(native(export, rel)))


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
    ibcmd = ""
    if not a.source_only:
        ibcmd = a.ibcmd or find_ibcmd(a.platform)
        if not ibcmd:
            report["error"] = "Не найден ibcmd платформы " + (a.platform or "1С") + "; укажите --ibcmd."
            return finish(2)
    tmp = tempfile.mkdtemp(prefix="partial-cf-")
    try:
        if a.since:
            changed, root, deleted = git_changes(export, a.since)
            report["changed"] = changed
            if root:
                report["root_changed"] = root
            if deleted:
                report["deleted"] = deleted
            objects += [o for o in changed if o not in objects]
        if not objects:
            report["error"] = "Нет изменённых объектов с " + a.since + "."
            return finish(1)
        out_cf = os.path.abspath(a.out) if a.out else ""
        settings = a.settings or (os.path.splitext(out_cf)[0] + ".merge-settings.xml" if out_cf else
                                  os.path.join(os.path.dirname(os.path.abspath(a.source_only)),
                                               os.path.basename(os.path.abspath(a.source_only)) + ".merge-settings.xml"))
        source = os.path.abspath(a.source_only) if a.source_only else os.path.join(tmp, "src")
        started = time.time()
        res = build(export, source, objects)
        write_file(settings, merge_settings(res))
        report.update({
            "selected": res.selected, "stubs_total": len(res.stubs),
            "stubs": [{"object": k, "referred_by": res.stubs[k].reason} for k in sorted(res.stubs)],
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
