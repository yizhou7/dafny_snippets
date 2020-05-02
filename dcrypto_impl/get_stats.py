import re
import sys

def print_stats(file_name):
	unique_opcodes = set()
	totoal_ins_count = 0

	with open(file_name) as f:
		for line in f.readlines():
			match = re.match(pattern, line)
			if match:
				instruciton = match.group(2)
				instruciton = instruciton.split(" ")
				# print(instruciton)
				totoal_ins_count += 1
				unique_opcodes.add(instruciton[0])

	print("file_name: " + file_name)
	print("totoal_ins_count: %d" % totoal_ins_count)
	print("uique_opcode_count: %d" % len(unique_opcodes))
	print("")

pattern = re.compile("(0x[0-9a-f]{8}),\t/\* (.+) \*/$")
print_stats(sys.argv[1])
