#!/usr/bin/env python3
"""Check conservation and PDF links; this is not a proof verifier."""
from collections import Counter, defaultdict
import csv
import hashlib
import json
from pathlib import Path
import re
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / "editorial"
KINDS = ("theorem", "proposition", "lemma", "corollary")
PDF_NAMES = {
    "main": "P1_V1_6_Main_Article_2026-10-31_EN.pdf",
    "companion": "P1_V1_6_Technical_Companion_2026-10-31_EN.pdf",
}


def groups(text):
    result, depth, start = [], 0, 0
    for index, char in enumerate(text):
        if char == "{":
            if depth == 0:
                start = index + 1
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                result.append(text[start:index])
    return result


def read_aux(path):
    result = {}
    for line in path.read_text().splitlines():
        if line.startswith("\\newlabel{"):
            outer = groups(line[len("\\newlabel"):])
            if len(outer) < 2:
                raise ValueError(f"Incomplete auxiliary record in {path}; rebuild both documents.")
            values = groups(outer[1])
            result[outer[0]] = dict(zip(
                ("number", "page", "title", "destination"), values[:4]))
    return result


baseline = json.loads((HERE / "v15_reference_baseline.json").read_text())
statement_baseline = json.loads((HERE / "v15_statement_baseline.json").read_text())
statement_pattern = re.compile(
    r"\\begin\{(theorem|proposition|lemma|corollary)\}.*?\\end\{\1\}", re.S)
statement_hashes = {}
locations, references = defaultdict(list), set()
counts, aux = {}, {}
for document in PDF_NAMES:
    texts = []
    for source in sorted((ROOT / f"{document}_sections").glob("*.tex")):
        text = source.read_text()
        texts.append(text)
        for match in statement_pattern.finditer(text):
            block = match.group(0)
            label = re.search(r"\\label\{([^}]+)\}", block).group(1)
            statement_hashes[label] = hashlib.sha256(block.encode()).hexdigest()
        for label in re.findall(r"\\label\{([^}]+)\}", text):
            locations[label].append((document, str(source.relative_to(ROOT))))
        references.update(re.findall(r"\\(?:ref|eqref|pageref)\{([^}]+)\}", text))
    all_text = "\n".join(texts)
    counts[document] = {
        kind: len(re.findall(r"\\begin\{" + kind + r"\}", all_text))
        for kind in (*KINDS, "proof")
    }
    aux[document] = read_aux(ROOT / "build" / f"resolved_{document}.aux.txt")

missing = sorted(set(baseline) - set(locations))
duplicates = {key: values for key, values in locations.items() if len(values) != 1}
unknown = sorted(references - set(locations))
rows = []
for label, old in sorted(baseline.items(), key=lambda item: (item[1]["old_document"], int(item[1]["page"]), item[0])):
    if label in missing or label in duplicates:
        continue
    document, source = locations[label][0]
    new = aux[document][label]
    rows.append({
        "repere": label, "type": old["kind"],
        "document_v1_5": old["old_document"],
        "numero_v1_5": old["number"], "page_v1_5": old["page"],
        "document_v1_6": document, "numero_v1_6": new["number"],
        "page_v1_6": new["page"], "titre_v1_5": old["title"],
        "fichier_v1_5": old["old_source"], "fichier_v1_6": source,
    })
for filename, selection in (
    ("correspondance_V1_5_V1_6.csv", rows),
    ("resultats_V1_5_V1_6.csv", [row for row in rows if row["type"] in KINDS]),
):
    with (HERE / filename).open("w", encoding="utf-8-sig", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(selection)

readers = {name: PdfReader(ROOT / "build" / filename) for name, filename in PDF_NAMES.items()}
by_filename = {PDF_NAMES[name]: reader for name, reader in readers.items()}
link_counts, bad_links, log_issues = {}, [], {}
for document, reader in readers.items():
    internal = external = 0
    for page_number, page in enumerate(reader.pages, 1):
        for annotation in page.get("/Annots", []):
            action = annotation.get_object().get("/A", {})
            destination = action.get("/D")
            if action.get("/S") == "/GoToR":
                external += 1
                target = action.get("/F")
                if target not in by_filename or destination not in by_filename[target].named_destinations:
                    bad_links.append([document, page_number, str(action)])
            elif action.get("/S") == "/GoTo":
                internal += 1
                if isinstance(destination, str) and destination not in reader.named_destinations:
                    bad_links.append([document, page_number, str(action)])
    link_counts[document] = {"internal": internal, "external": external}
    log = (ROOT / "build" / f"resolved_{document}.log.txt").read_text(errors="replace")
    log_issues[document] = {word: log.lower().count(word.lower()) for word in (
        "Overfull", "Underfull", "undefined", "multiply defined")}

original_counts = Counter(item["kind"] for item in baseline.values())
count_match = all(sum(counts[doc][kind] for doc in counts) == original_counts[kind] for kind in KINDS)
number_changes = [row for row in rows if row["type"] in KINDS and
                  (row["document_v1_5"] != row["document_v1_6"] or
                   row["numero_v1_5"] != row["numero_v1_6"])]
text_changes = sorted(label for label, record in statement_baseline.items()
                      if statement_hashes.get(label) != record["sha256"])
extra_statements = sorted(set(statement_hashes) - set(statement_baseline))
preservation = {
    "baseline": "P1 V1.5", "edition": "P1 V1.6",
    "compared_statements": len(statement_baseline),
    "modified_or_missing_statements": text_changes,
    "additional_statements": extra_statements,
    "status": "passed" if not text_changes and not extra_statements else "failed",
    "scope": "Exact LaTeX text of theorem, proposition, lemma and corollary environments; not a proof checker.",
}
(HERE / "statement_text_preservation.json").write_text(
    json.dumps(preservation, ensure_ascii=False, indent=2) + "\n")
passed = (not number_changes and not missing and not duplicates and not unknown and not bad_links and count_match
          and not text_changes and not extra_statements
          and all(not item["undefined"] and not item["multiply defined"] and not item["Overfull"]
                  for item in log_issues.values()))
report = {
    "status": "passed" if passed else "failed",
    "scope": "Source conservation, reference resolution and link targets only; not mathematical certification.",
    "baseline_version": "P1 V1.5, 31 October 2026, main 62 pages and companion 96 pages",
    "original_labels": len(baseline), "new_labels": len(locations),
    "missing_labels": missing, "duplicate_labels": duplicates,
    "unknown_references": unknown, "statement_counts": counts,
    "statement_counts_preserved": count_match,
    "statement_number_changes": number_changes,
    "statement_text_preservation": preservation,
    "pages": {name: len(reader.pages) for name, reader in readers.items()},
    "links": link_counts, "bad_link_targets": bad_links, "logs": log_issues,
}
(HERE / "references_audit.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
metrics = {
    "MainPageCount": report["pages"]["main"],
    "CompanionPageCount": report["pages"]["companion"],
    "PreservedLabelCount": len(baseline),
    "CurrentLabelCount": len(locations),
    "NumberedResultCount": sum(original_counts[k] for k in KINDS),
    "CrossDocumentLinkCount": sum(item["external"] for item in link_counts.values()),
    "InternalLinkCount": sum(item["internal"] for item in link_counts.values()),
}
(HERE / "production_metrics.tex").write_text("".join(
    "\\newcommand{\\" + key + "}{" + str(value) + "}\n"
    for key, value in metrics.items()))
print(json.dumps(report, ensure_ascii=False, indent=2))
if not passed:
    raise SystemExit(1)
