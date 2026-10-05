"""Collect the overview and its local proof dependencies, without build debris."""
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parent
SEEDS = [
    "VYSLEDKY.tex",
    "size_bounds/QUADRATIC_PROOF_GUIDE.txt",
    "independent_directions/FIXED_K_PROOF_GUIDE.txt",
    "size_bounds/FIXED_K_PROOF_GUIDE.txt",
    "independent_directions/ENDPOINT_PROFILE_PROOF_GUIDE.txt",
]
all_tex = list(ROOT.rglob("*.tex"))
by_name = {}
for path in all_tex:
    by_name.setdefault(path.name, []).append(path)


def resolve_reference(owner, name):
    for path in (owner.parent / name, ROOT / name):
        path = path.resolve()
        if path.is_relative_to(ROOT) and path.is_file():
            return path
    matches = by_name.get(Path(name).name, [])
    return matches[0] if len(matches) == 1 else None


selected = set()
pending = [ROOT / name for name in SEEDS]
unresolved = set()
while pending:
    path = pending.pop().resolve()
    if path in selected:
        continue
    if not path.is_file():
        raise FileNotFoundError(path)
    selected.add(path)
    content = path.read_text().replace(r"\_", "_")
    for name in re.findall(r"[A-Za-z0-9_./-]+\.tex", content):
        dependency = resolve_reference(path, name)
        if dependency is not None:
            pending.append(dependency)
        else:
            unresolved.add(name)

missing_pdfs = []
for path in list(selected):
    if path.suffix == ".tex":
        pdf = path.with_suffix(".pdf")
        if pdf.is_file():
            selected.add(pdf)
        else:
            missing_pdfs.append(str(path.relative_to(ROOT)))

# The asymptotic singularity counterexample cites a fixed published seed.
# Include its exact certificates and their local imports, without collecting
# unrelated historical experiment outputs from the working directory.
if ROOT / "size_bounds/all_gap_singularity_inheritance.tex" in selected:
    for name in (
        "size_bounds/certify_all_gap_singularity.py",
        "size_bounds/certify_all_gap_power_singularity.py",
        "size_bounds/diagnostic_all_gap_rank.py",
        "size_bounds/diagnostic_endpoint_rank.py",
        "size_bounds/all_gap_singularity_certificate.json",
        "size_bounds/all_gap_power_singularity_certificate.json",
        "equal_size/meyer_2023_five_dice_sixty.json",
    ):
        path = ROOT / name
        if not path.is_file():
            raise FileNotFoundError(path)
        selected.add(path)

for name in ("PROOF_INDEX.txt", "ASYMPTOTIC_STATUS.txt", "FINAL_REVIEW.txt",
             "size_bounds/QUADRATIC_ANALYTIC_PROOF_GUIDE.txt"):
    path = ROOT / name
    if path.exists():
        selected.add(path)

manifest = ROOT / "BUNDLE_CONTENTS.txt"
manifest.write_text(
    "VYBER DUKAZU / PROOF BUNDLE\n"
    "Start with VYSLEDKY.pdf and PROOF_INDEX.txt, then the *_PROOF_GUIDE.txt files.\n"
    "Paths retain the layout of research/2026-09-30/.\n"
    "Older notes are included only when a selected proof references them.\n"
    "Published external inputs and the original manuscript are cited, not bundled.\n"
    "Source-only historical notes are listed at the end; they are not needed for the current proofs.\n\n"
    "The fixed published seed and exact certificates support an all-n rank obstruction;\n"
    "they are not a new small-n optimization or search. With Python 3 and SymPy,\n"
    "run certify_all_gap_singularity.py and then certify_all_gap_power_singularity.py\n"
    "from size_bounds/.\n\n"
    + "\n".join(str(path.relative_to(ROOT)) for path in sorted(selected))
    + "\n\nSource-only historical notes:\n" + "\n".join(sorted(missing_pdfs)) + "\n"
)
selected.add(manifest)
archive = ROOT / "HLAVNI_DUKAZY.zip"
with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as bundle:
    for path in sorted(selected):
        bundle.write(path, path.relative_to(ROOT))
with zipfile.ZipFile(archive) as bundle:
    if bundle.testzip() is not None:
        raise RuntimeError("Archive integrity check failed")

stale = [
    str(path.relative_to(ROOT))
    for path in selected
    if path.suffix == ".tex"
    and path.with_suffix(".pdf").exists()
    and path.with_suffix(".pdf").stat().st_mtime < path.stat().st_mtime
]
print(f"Included {len(selected)} files; archive {archive.stat().st_size:,} bytes")
print("Stale PDFs:", stale)
print("Source-only historical notes:", sorted(missing_pdfs))
print("External/unresolved source references:", sorted(unresolved))
