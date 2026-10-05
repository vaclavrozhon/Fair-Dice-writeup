"""Independent integer DP of all stored small three-wise fair words."""
import itertools,json
from pathlib import Path
root=Path(__file__).parent
out={}
for n,name in [(3,'three'),(4,'four')]:
 words=(root/f'{name}_dice_six_canonical_words.txt').read_text().split()
 assert len(words)==len(set(words))
 for w in words:
  counts={():1}
  for c in w:
   for t,v in list(counts.items()):
    if len(t)<3 and c not in t:counts[t+(c,)]=counts.get(t+(c,),0)+v
  for k,expected in [(1,6),(2,18),(3,36)]:
   assert all(counts[t]==expected for t in itertools.permutations(map(str,range(n)),k))
 out[n]={'words_verified':len(words),'pair_count':18,'triple_count':36}
(root/'small_enumeration_verified.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
