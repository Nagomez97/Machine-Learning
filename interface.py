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
	def exec_game(self, file):
		outfile = open("output", "w")
		output = subprocess.call(['sbcl', '--script', file], stdout=outfile)
		outfile.close()

		return self.get_wins_score()

	"""Gets the winner of a match
	"""
	def get_wins_score(self):
		r = open("output", "r")
		ls = r.readlines()

		# Score line
		line = [ls[3+(5*i)].split() for i in range(4)]

		
		# Results
		p1 = [int(line[i][2]) for i in range(4)]
		p2 = [int(line[i][4]) for i in range(4)]

		print('\nmatch')
		print('p1:', p1)
		print('p2:', p2)

		wins = 0
		score = 0
		for i in range(4):
			if i%2 == 1: # matches where it plays first
				score += p1[i]
				if p1[i] > p2[i]:
					wins += 1
					score += 1000

			elif i%2 == 0: # matches where it plays second
				score += p2[i]
				if p2[i] > p1[i]:
					wins += 1
					score += 1000
					
		return (wins, score)