from random import *

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

		ret = '\n(defun heuristica (estado)\n'
		ret += '(+ ' + bias
		ret += '(prod-escalar ' + weightVector
		ret += '(suma-vectores ' + biasVector
		ret += '(matriz-x-vector ' + weightMatrix + inputs + ')))))'

		ret += "\n\n\n"
		ret += "(defvar *"+self.name+"* (make-jugador \n\t:nombre   '|"+self.name+"|\n\t:f-juego  #'f-j-nmx\n\t:f-eval   #'heuristica))\n\n"
		ret += "(partida 0 2 (list *jdr-nmx-Regular*	*"+self.name+"*))"
		ret += "(partida 0 2 (list *"+self.name+"*		*jdr-nmx-Regular*))"
		ret += "(partida 0 2 (list *jdr-nmx-Bueno*      *"+self.name+"*))"
		ret += "(partida 0 2 (list *"+self.name+"*		*jdr-nmx-Bueno*))"

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
		player.weightMatrix = [[(random()*2) for i in range(numInputs)] for j in range(numNeurons)]
		player.biasVector = [(random()*2) for i in range(numNeurons)]

		# Hidden to output function
		player.weightVector = [(random()*2) for i in range(numNeurons)] 
		player.bias = random()*2

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
	def new_generation(player1, player2, population, numNeurons, numInputs):
		newGen = []
		newGen.append(player1)
		newGen.append(player2)
		# Introduce a new random player
		newGen.append(random_player(numNeurons, numInputs))
		# Combine new players
		newGen += combine_players(player1, player2, population-3, numNeurons, numInputs)

	""" Combine two players and generates a list of children
	:param player1, player2
	:param numChildren: number of combined children
	:param numNeurons, numInputs

	returns a list of children as a result of p1 and p2 combinations
	"""
	@staticmethod
	def combine_players(player1, player2, numChildren, numNeurons, numInputs):
		# Empty children
		children = [Player() for i in numChildren]
			
		for i in numInputs:
			# Combining weightMatrix
			for n in numNeurons:
				for c in children:
					c.weightMatrix[i][n] = combine_element(player1.weightMatrix[i][n], player2.weightMatrix[i][n])
			# Combining biasVector and weightVector
			for c in children:
				c.weightVector[i] = combine_element(player1.weightVector[i], player2.weightVector[i])
				c.biasVector[i] = combine_element(player1.biasVector[i], player2.biasVector[i])
		
		# Combining biases
		for c in children:
			c.bias = combine_element(player1.bias, player2.bias)

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
		a = rand()
		if(a < 0.475):
			return num1
		elif(a < 0.95):
			return num2
		else:
			return (random()*2 - 1)
