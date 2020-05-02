import re
import glob

def print_stats(file_name):
	unique_opcodes = set()
	totoal_ins_count = 0

	with open(file_name) as f:
		for line in f.readlines():
			if re.match(pattern, line):
				totoal_ins_count += 1
				line = line.strip().split("\t")
				unique_opcodes.add(line[0])

	print("file_name: " + file_name)
	print("totoal_ins_count: %d" % totoal_ins_count)
	print("uique_opcode_count: %d" % len(unique_opcodes))
	print("")

s_files = sorted(glob.glob("*.s"))
pattern = re.compile("^\t[a-z]")

for s_file in s_files:
	print_stats(s_file)
