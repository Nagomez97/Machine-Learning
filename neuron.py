class Neuron(object):
	""" Neuron init
	:param player (Player): player the neuron belongs to
	:param layer (int): 
	"""
	def __init__(self, player, layer, name):
		self.player = player
		self.layer = layer
		self.name = name
