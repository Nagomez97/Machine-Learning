from random import *


class Neuron(object):
	""" Neuron init
	:param player (Player): player the neuron belongs to
	:param layer (int): layer neuron
	:param name: name of the function the neuron is evaluating
	"""
	def __init__(self, player, layer, name):
		self.player = player
		self.layer = layer
		self.name = name

		# Genera un array de pesos aleatorios entre -1 y 1
		# de la misma longitud que el layer anterior (un peso por neurona)
		self.weights = [(random()*2 - 1) for i in range(len(player.layers[layer-1]))]

		# Queda pendiente estudiar el bias
		self.bias = random()*2 - 1

	def __str__(self):
		s = ''

		(defun prod (tablero lado ws cont)
			(+ (* (first ws) (get-fichas tablero lado cont))
				(prod tablero lado (rest ws) (rest inps) (+ cont 1))))

		(+ (* w0 (neuron0))
			(*)...)


		(defun )