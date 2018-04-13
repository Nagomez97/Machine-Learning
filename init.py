import player
import interface

p = player.Player.random_player("test", 14, 14)
r = open('mancala.cl', 'r').read()
f = open('test.cl', 'w')
f.write(r + str(p))
f.close()

game = interface.Interface()
print(game.exec_game())
