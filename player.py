

class Player(object):

	""" Player init
	:param name: current player name
	:param layers: list with layers and neurons

	E.G:
		A 3 layer network should be specified as:
			numLayers = 3
			numNeurons = [5, 5, 3]
	"""
	def __init__(self, name, layers):
		# Matrix of layers x neurons [layer][neuron]
		self.layers = layers
		self.name = name


	""" Combine a list of players, adding newGenPlayers new ones
	:param listPlayers: list with mutable players
	:param newGenPlayers: number of new players we want to generate

	"""
	def combine_players(self, listPlayers, newGenPlayers):

		for i in range(len(listPlayers)):
			for j in range(len(listPlayers[i])):
				Neuron.combine_neurons()
