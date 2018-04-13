import subprocess

directory = "/Desktop/Machine-Learning/Players"

class Interface(object):
	"""Interface to use Lisp SBCL"""

	def __init__(self):
		pass

	"""Executes the game and returns the winner
	0: draw
	1: p1 wins
	2: p2 wins
	"""
	def exec_game(self):
		outfile = open("output", "w")
		output = subprocess.call(['sbcl', '--script', 'test.cl'], stdout=outfile)
		outfile.close()

		return self.get_winner()

	"""Gets the winner of a match
	"""
	def get_winner(self):
		r = open("output", "r")
		ls = r.readlines()

		# Score line
		line = ls[-2].split() # -2 cause there's no \n
		
		# Results
		p1 = int(line[2])
		p2 = int(line[4])

		if p1 > p2:
			return 1
		elif p1 < p2:
			return 2
		else:
			return 0

