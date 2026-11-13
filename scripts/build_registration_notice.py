#!/usr/bin/env python3
"""Rebuild the documentary edition with the audited, contained TeX builder."""
from pathlib import Path
import argparse,json
from build_manuscript_v20 import build
from build_publication import bibliography_inventory

ROOT=Path(__file__).resolve().parents[1]
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=ROOT/'output/pdf/registration-notice')
    parser.add_argument('--evidence-dir',type=Path,required=True)
    args=parser.parse_args()
    package=ROOT/json.loads((ROOT/'manuscripts/paper-p1/REGISTRATION_NOTICE_CURRENT.json').read_text())['package']
    source=package/'sources';bibliography_inventory(source)
    build(args.output_dir.resolve(),args.evidence_dir.resolve(),source=source,
          names={'main':'P1_Main_EN.pdf','companion':'P1_Companion_EN.pdf'},expected_tex_files=34)
