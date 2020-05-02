import sys
import re

pattern = re.compile("^\t[a-z]")

unique_opcodes = set()
totoal_ins_count = 0

with open(sys.argv[1]) as f:
	for line in f.readlines():
		if re.match(pattern, line):
			totoal_ins_count += 1
			line = line.strip().split("\t")
			unique_opcodes.add(line[0])

print("totoal_ins_count: %d" % totoal_ins_count)
print("uique_opcode_count: %d" % len(unique_opcodes))
# print(unique_opcodes)