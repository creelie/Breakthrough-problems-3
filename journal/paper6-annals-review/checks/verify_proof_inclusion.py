"""Verify faithful proof-page inclusion, not the truth of its mathematics."""
from pathlib import Path
from pypdf import PdfReader
import sys,hashlib,json

def verify(pdf,source):
    assert hashlib.sha256(source.read_bytes()).hexdigest()=='f919b57829b178c8e60e7c17b018cf773e7907cf642ef5a3347d8a826e8dbf18'
    reader=PdfReader(pdf);original=PdfReader(source);found=[]
    assert len(original.pages)==49
    for i,p in enumerate(reader.pages):
        for obj in p.get('/Resources',{}).get('/XObject',{}).values():
            form=obj.get_object()
            if 'OpenAI-QRH-11-12.pdf' in str(form.get('/PTEX.FileName','')):
                found.append((i,int(form['/PTEX.PageNumber']),form.get_data()))
    assert len(found)==49
    start=found[0][0]
    for j,(i,n,stream) in enumerate(found):
        assert i==start+j and n==j+1
        assert stream==original.pages[j].get_contents().get_data()
    first=reader.pages[0].extract_text()
    assert 'Deep Bhattacharjee' in first and 'Ushashi Bhattacharya' in first
    return {'pages':len(reader.pages),'proof_pages':49,'source_drawing_streams_match':True,
            'scope':'Content inclusion integrity; not an independent verification of the analytic proof.'}

if __name__=='__main__':
    print(json.dumps(verify(Path(sys.argv[1]),Path(sys.argv[2]))))
