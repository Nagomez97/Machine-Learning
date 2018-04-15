import subprocess
import tempfile
import player

class Tournament(object):
	"""docstring for Tournament"""
	def __init__(self, players):
		self.players = players
		self.mandatory_players = [player.Player('jdr-nmx-Regular'), player.Player('jdr-nmx-Bueno')]
		self.scores = {p: {'w': 0, 'd': 0, 'l': 0, 's': 0, 'm': 0} for p in players}
		for p in self.mandatory_players:
			self.scores[p] = {'w': 0, 'd': 0, 'l': 0, 's': 0, 'm': 0}

	def ranking (self):
		# result = sorted(self.scores.items(), key=lambda x: x[1]['s'], reverse=True)
		# result = sorted(result, key=lambda x: x[1]['d'], reverse=True)
		# result = sorted(result, key=lambda x: x[1]['w'], reverse=True)
		# result = sorted(result, key=lambda x: x[1]['m'], reverse=True)
		result = sorted(self.scores.items(), key=lambda x: [x[1]['m'], x[1]['w'], x[1]['d'], x[1]['s']], reverse=True)
		return result

	def all_vs_all (self):
		# matches between players
		for i, p1 in enumerate(self.players):
			rest = [self.players[j] for j in range(i+1, len(self.players))]
			for p2 in rest:
				print(p1.name, 'vs', p2.name)
				self.match(p1, p2)
		# matches against mandatory players
		for mp in self.mandatory_players:
			for p in self.players:
				print(p.name, 'vs', mp.name)
				self.match(mp, p)

	def match (self, p1, p2):
		file_name = 'players/' + p1.name + '_vs_' + p2.name + '.cl'
		lisp_file = open(file_name, 'w+')
		content = open('players/mancala.cl', 'r').read()

		# File with the game, the players and two matches
		if p1 not in self.mandatory_players:
			content += str(p1)
		if p2 not in self.mandatory_players:
			content += str(p2)
		lisp_file.write(content + '\n')
		lisp_file.write('(partida 0 2 (list *' + p1.name + '*		*' + p2.name + '*))\n')
		lisp_file.write('(partida 0 2 (list *' + p2.name + '*		*' + p1.name + '*))\n')

		lisp_file.close()

		# Play the games
		results = subprocess.getoutput('sbcl --script ' + file_name + ' | grep Marcador')
		## print(results, end='\n\n')
		results = results.split()
		scores = []
		scores.append([int(results[2]), int(results[4])])
		scores.append([int(results[8]), int(results[10])])

		# Add to scores
		if scores[0][0] > scores[0][1]: 	# Match 0 (p1 vs p2) p1 wins
			self.scores[p1]['w'] += 1
			self.scores[p1]['s'] += scores[0][0]
			self.scores[p2]['l'] += 1
			self.scores[p2]['s'] += scores[0][1]
			if p2 in self.mandatory_players:
				self.scores[p1]['m'] += 1
		elif scores[0][0] < scores[0][1]: 	# Match 0 (p1 vs p2) p2 wins
			self.scores[p2]['w'] += 1
			self.scores[p2]['s'] += scores[0][1]
			self.scores[p1]['l'] += 1
			self.scores[p1]['s'] += scores[0][0]
			if p1 in self.mandatory_players:
				self.scores[p2]['m'] += 1
		else: 								# Match 0 (p1 vs p2) draw
			self.scores[p1]['d'] += 1
			self.scores[p1]['s'] += scores[0][0]
			self.scores[p2]['d'] += 1
			self.scores[p2]['s'] += scores[0][1]

		if scores[1][0] > scores[1][1]: 	# Match 1 (p2 vs p1) p2 wins
			self.scores[p2]['w'] += 1
			self.scores[p2]['s'] += scores[1][0]
			self.scores[p1]['l'] += 1
			self.scores[p1]['s'] += scores[1][1]
			if p1 in self.mandatory_players:
				self.scores[p2]['m'] += 1
		elif scores[1][0] < scores[1][1]: 	# Match 1 (p2 vs p1) p1 wins
			self.scores[p1]['w'] += 1
			self.scores[p1]['s'] += scores[1][1]
			self.scores[p2]['l'] += 1
			self.scores[p2]['s'] += scores[1][0]
			if p2 in self.mandatory_players:
				self.scores[p1]['m'] += 1
		else: 								# Match 1 (p2 vs p1) draw
			self.scores[p2]['d'] += 1
			self.scores[p2]['s'] += scores[1][0]
			self.scores[p1]['d'] += 1
			self.scores[p1]['s'] += scores[1][1]

		subprocess.run(['rm', file_name])
