grep ^DEBUG2AA: log.txt |cut -d: -f2- |sort -u   > src/gen2.ml
grep ^DEBUG2A: log.txt |cut -d: -f2- |sort -u    >> src/gen2.ml
grep ^DEBUG2B: log.txt |cut -d: -f2-  |sort -u   >> src/gen2.ml
grep ^DEBUG2C: log.txt |cut -d: -f2-             >> src/gen2.ml
