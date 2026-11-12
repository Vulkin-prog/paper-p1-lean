#!/usr/bin/env python3
"""Rebuild the publication edition with the audited repository TeX builder."""
from pathlib import Path
import argparse,re
from build_manuscript_v20 import build

ROOT=Path(__file__).resolve().parents[1]
PACKAGE=ROOT/'manuscripts/paper-p1/publication-2026-11-12'
SOURCE=PACKAGE/'sources'
NAMES={'main':'P1_Main_EN.pdf','companion':'P1_Companion_EN.pdf'}

def bibliography_inventory(source=SOURCE):
    master=(source/'bibliography.tex').read_text()
    matches=list(re.finditer(r'\\bibitem\{([^}]+)\}',master))
    keys=[m[1] for m in matches]
    if len(keys)!=len(set(keys)) or len(keys)!=31:
        raise ValueError('The publication master must contain31 distinct bibliography entries')
    end=master.index(r'\end{thebibliography}')
    entries={m[1]:master[m.start():matches[i+1].start() if i+1<len(matches) else end].strip() for i,m in enumerate(matches)}
    def expanded(path,seen):
        path=path.resolve()
        if not path.is_relative_to(source.resolve()) or not path.is_file():
            raise ValueError('Nonlocal bibliography input')
        if path in seen:return ''
        seen.add(path)
        text=re.sub(r'(?<!\\)%[^\n]*','',path.read_text())
        return text+'\n'+'\n'.join(expanded(source/(n+'.tex'),seen)
            for n in re.findall(r'\\input\{([^}]+)\}',text) if not n.startswith('bibliography'))
    inventory={}
    for doc,expected_count in [('main',18),('companion',16)]:
        groups=re.findall(r'\\cite(?:\[[^]]*\])*\{([^}]+)\}',expanded(source/(doc+'.tex'),set()))
        cited={k.strip() for g in groups for k in g.split(',')}
        if cited-set(entries):raise ValueError('Missing cited bibliography key')
        selected=[key for key in keys if key in cited]
        expected=('% Generated from bibliography.tex by build.py.\n'
            '\\begin{thebibliography}{99}\n\\addcontentsline{toc}{section}{References}\n\n'
            +'\n\n'.join(entries[k] for k in selected)+'\n\n\\end{thebibliography}\n')
        if len(selected)!=expected_count or (source/f'bibliography_{doc}.tex').read_text()!=expected:
            raise ValueError('Document-specific bibliography differs from its exact cited master subset: '+doc)
        inventory[doc]=selected
    return inventory

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=PACKAGE/'pdf')
    parser.add_argument('--evidence-dir',type=Path,required=True)
    args=parser.parse_args()
    bibliography_inventory()
    build(args.output_dir.resolve(),args.evidence_dir.resolve(),source=SOURCE,names=NAMES,expected_tex_files=34)
