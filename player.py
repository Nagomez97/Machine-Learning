

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

	""" Generates a random player (only one output)
	:param numNeurons: number of neurons in hidden layer
	:param numInputs: number of inputs

	returns a new random player (Player)
	"""
	def random_player(numNeurons, numInputs):
		player = Player(name)

		# Input to hidden function
		player.weightMatrix = [[(random()*2 - 1) for i in numInputs] for j in numNeurons]
		player.biasVector = [(random()*2 - 1) for i in numNeurons]

		# Hidden to output function
		player.weightVector = [(random()*2 - 1) for i in numNeurons] 
		player.bias = random()*2 - 1

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
	def new_generation(player1, player2, population, numNeurons, numInputs):
		newGen = []
		newGen.append(player1)
		newGen.append(player2)
		newGen.append(random_player(numNeurons, numInputs))

		# Combining players


	""" Combine two players and generates a list of children
	:param player1, player2
	:param numChildren: number of combined children
	:param numNeurons, numInputs

	returns a list of children as a result of p1 and p2 combinations
	"""
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