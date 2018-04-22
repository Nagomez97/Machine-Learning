from random import *
import pickle

class Player(object):

	""" Player init
	:param name: current player name
	:param layers: list with layers and neurons

	E.G:
		A 3 layer network should be specified as:
			numLayers = 3
			numNeurons = [5, 5, 3]
	"""
	def __init__(self, name):
		# Matrix of layers x neurons [layer][neuron]
		self.name = name
		self.weightMatrix = None
		self.biasVector = None

		self.weighVector = None
		self.bias = None

	def __str__(self):
		bias = str(self.bias)
		weightVector = "'" + str(self.weightVector).replace("[", "(").replace(']',')\n').replace(',', '')
		weightMatrix = "'" + str(self.weightMatrix).replace("[", "(").replace(']',')\n').replace(',', '')
		biasVector = "'" + str(self.biasVector).replace("[", "(").replace(']',')\n').replace(',', '').rstrip("\n")
		inputs = '(inputs estado)'
		heuristica = 'h_'+self.name

		ret = '\n(defun ' + heuristica + ' (estado)\n'
		ret += '(+ ' + bias
		ret += '\n(prod-escalar ' + weightVector
		ret += '(suma-vectores ' + biasVector
		ret += '\n(matriz-x-vector ' + weightMatrix + inputs + ')))))'

		ret += "\n\n\n"
		ret += "(defvar *"+self.name+"* (make-jugador \n\t:nombre   '|"+self.name+"|\n\t:f-juego  #'f-j-nmx\n\t:f-eval   #'" + heuristica + "))\n\n"

		return ret		

	""" Generates a random player (only one output)
	:param numNeurons: number of neurons in hidden layer
	:param numInputs: number of inputs

	returns a new random player (Player)
	"""
	@staticmethod
	def random_player(name, numNeurons, numInputs):
		player = Player(name)

		# Input to hidden function
		player.weightMatrix = [[(uniform(-1, 1)) for i in range(numInputs)] for j in range(numNeurons)]
		player.biasVector = [(uniform(-1, 1)) for i in range(numNeurons)]

		# Hidden to output function
		player.weightVector = [(uniform(-1, 1)) for i in range(numNeurons)] 
		player.bias = uniform(-1, 1)

		return player


	""" Combine a list of players, adding newGenPlayers new ones
	and creates a new generation
	:param player1, player2: top two players of previous generation.
							We will combine them.
	:param population: number of players in the new generation
	:param numNeurons: number of neurons in hidden layer
	:param numInputs: number of inputs
	
	returns a list of mutated players (generated or combined):
		player1
		player2
		randomPlayer
		population - 3 combined players
	"""
	@staticmethod
	def new_generation(gen, player1, player2, population, numNeurons, numInputs, players=[]):
		newGen = []
		newGen.append(player1)
		newGen.append(player2)
		newGen += players
		newPlayers = population-3-len(players)
		# Introduce a new random player
		name = 'gen' + str(gen) + 'player'
		newGen.append(Player.random_player(name + '2', numNeurons, numInputs))
		# Generate names
		names = [name + str(i+3+len(players)) for i in range(newPlayers)]
		# Combine new players
		newGen += Player.combine_players(player1, player2, newPlayers, numNeurons, numInputs, names)
		return newGen

	""" Combine two players and generates a list of children
	:param player1, player2
	:param numChildren: number of combined children
	:param numNeurons, numInputs

	returns a list of children as a result of p1 and p2 combinations
	"""
	@staticmethod
	def combine_players(player1, player2, numChildren, numNeurons, numInputs, names):
		# Empty children
		children = [Player(names[i]) for i in range(numChildren)]
		# for c in children:
		# 	c.weightMatrix = [[None]*numNeurons]*numInputs
		# 	c.weightVector = [None]*numInputs
		# 	c.biasVector = [None]*numInputs

		# for i in range(numInputs):
		# 	# Combining weightMatrix
		# 	for n in range(numNeurons):
		# 		for c in children:
		# 			c.weightMatrix[i][n] = Player.combine_element(player1.weightMatrix[i][n], player2.weightMatrix[i][n])
		# 	# Combining biasVector and weightVector
		# 	for c in children:
		# 		c.weightVector[i] = Player.combine_element(player1.weightVector[i], player2.weightVector[i])
		# 		c.biasVector[i] = Player.combine_element(player1.biasVector[i], player2.biasVector[i])
		
		# # Combining biases
		# for c in children:
		# 	c.bias = Player.combine_element(player1.bias, player2.bias)
		wm1 = player1.weightMatrix
		wm2 = player2.weightMatrix
		bv1 = player1.biasVector
		bv2 = player2.biasVector
		wv1 = player1.weightVector
		wv2 = player2.weightVector
		b1 = player1.bias
		b2 = player2.bias
		for c in children:
			c.weightMatrix = [[Player.combine_element(wm1[i][j], wm2[i][j]) for j in range(numInputs)] for i in range(numNeurons)]
			c.biasVector = [Player.combine_element(bv1[i], bv2[i]) for i in range(numNeurons)]
			c.weightVector = [Player.combine_element(wv1[i], wv2[i]) for i in range(numNeurons)]
			c.bias = Player.combine_element(b1, b2) 
		return children


	""" Combine two elements with a random probability
	:param num1: first element to combine
	:param num2: second element to combine

	Probabilities: 
		Return a random number: 5%
		Return the first number: 47.5%
		Return the second number: 47.5%
	"""
	@staticmethod
	def combine_element(num1, num2):
		a = random()
		if(a < 0.475):
			return num1
		elif(a < 0.95):
			return num2
		else:
			return uniform(-1, 1)


	def save (self):
		output = open('players/last_run/' + self.name + '.pkl', 'wb+')
		pickle.dump(self, output, pickle.HIGHEST_PROTOCOL)
		output.close()

	@staticmethod
	def load (file):
		input = open(file, 'rb')
		return pickle.load(input)
