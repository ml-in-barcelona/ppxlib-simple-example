grep ^DEBUG2AA: log.txt |cut -d: -f2- |sort -u   > src/gen2.ml
grep ^DEBUG2A: log.txt |cut -d: -f2- |sort -u    >> src/gen2.ml
grep ^DEBUG2B: log.txt |cut -d: -f2-  |sort -u   >> src/gen2.ml
grep ^DEBUG2C: log.txt |cut -d: -f2-             >> src/gen2.ml

cat src/gen2.ml \
    | sed -e 's/: list//g' \
    | sed -e 's/:.list.//g' \
    | sed -e 's/: option//g' \
    | sed -e "s/:.string.option.//g" \
    | sed -e "s/:.rec_flag.list.//g" \
    | sed -e '$d' \
	  > src/gen3.ml
rm src/gen2.ml
