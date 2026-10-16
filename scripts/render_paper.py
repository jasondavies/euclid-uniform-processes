"""Render the LaTeX source as self-contained HTML with native MathML and citations."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
source = (root / 'paper/short-gcd-certificates.tex').read_text()
# Citeproc renders the BibTeX entry; omit the duplicate manual LaTeX bibliography.
start = source.index(r'\begin{thebibliography}')
end = source.index(r'\end{thebibliography}') + len(r'\end{thebibliography}')
source = source[:start] + source[end:]
subprocess.run(['pandoc', '-f', 'latex', '-s', '--mathml', '--citeproc',
                '--bibliography', str(root / 'paper/references.bib'),
                '--csl', str(root / 'paper/numeric.csl'),
                '--metadata', 'link-citations=true',
                '--metadata', 'reference-section-title=References',
                '--css', str(root / 'paper/style.css'), '--embed-resources',
                '-o', str(root / 'paper/short-gcd-certificates.html')],
               input=source, text=True, check=True)
