"""Check a single coherent manuscript and exact attribution, not mathematical truth."""
from pathlib import Path
import sys,json,re
from pypdf import PdfReader

def verify(pdf,tex):
    s=tex.read_text(encoding='utf-8');r=PdfReader(pdf)
    assert len(re.findall(r'\\title(?:\[[^\n]*\])?\{',s))==1
    assert '\\includepdf' not in s and '\\usepackage{pdfpages}' not in s
    assert 'Consequence of OpenAI, {\\cite[Theorem 1.1]{OAI26}}' in s
    assert '\\label{thm:zerofree}' in s
    assert 'no new independent proof of it is\nclaimed here.' in s
    borrowed=[]
    for i,p in enumerate(r.pages):
        for obj in p.get('/Resources',{}).get('/XObject',{}).values():
            form=obj.get_object();name=str(form.get('/PTEX.FileName',''))
            if 'OpenAI-QRH' in name or 'paper2.pdf' in name:borrowed.append(i+1)
    assert not borrowed,'A third-party article is still embedded'
    first=r.pages[0].extract_text()
    assert 'Deep Bhattacharjee' in first and 'Ushashi Bhattacharya' in first
    assert '/OpenAI' not in str(r.metadata.get('/Author',''))
    assert 'OpenAI' not in str(r.metadata.get('/Author',''))
    assert len(r.pages)<40,'Unexpected manuscript expansion requires review'
    return {'pages':len(r.pages),'embedded_third_party_article_pages':0,
            'single_manuscript':True,'precise_zero_free_theorem_citation':True,
            'both_original_authors_present':True,'scope':'Structure and attribution only; full proof audit has its own result.'}

if __name__=='__main__':print(json.dumps(verify(Path(sys.argv[1]),Path(sys.argv[2]))))
