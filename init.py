import sys
import player
import interface

# Para mas adelante elegir cuantas generaciones se crean en la ejecucion
if len(sys.argv) == 2:
	numGens = sys.argv[1]
else:
	numGens = 1

# Mancala en lisp
r = open('mancala.cl', 'r').read()

# Funciones para jugar y sacar ganadores
game = interface.Interface()

# Generacion original
gen = 0
n = 'gen' + str(gen) + 'player'
players = [player.Player.random_player(n + str(i), 14, 14) for i in range(10)]

ranking = ['    name    - wins - score']
for i, p in enumerate(players):
	name = n + str(i)
	file = 'players/' + name + '.cl'
	f = open(file, 'w+')
	f.write(r + str(p))
	f.close()

	wins, score = game.exec_game(file)
	ranking.append(name + ' -   ' + str(wins) + '  - ' + str(score))

ranking_file = open('players/ranking', 'w+')

ranking.sort(key=lambda score: score.split()[4], reverse=True) # sorts ranking by wins
ranking_file.write('\n'.join(ranking))

ranking_file.close()