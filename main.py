import sys
import player
import tournament

# Para mas adelante elegir cuantas generaciones se crean en la ejecucion
if len(sys.argv) == 2:
	numGens = int(sys.argv[1])
else:
	numGens = 1
if len(sys.argv) == 3:
	if sys.argv[1] == '--lisp':
		p = player.Player.load(sys.argv[2])
		f = open(p.name + '.cl', 'w+')
		f.write(str(p))
		f.close()
		print('generated', p.name + '.cl')
		sys.exit()

# Generacion original
gen = 0

print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
print('X                         Generación 0                            X')
print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')

n = 'gen' + str(gen) + 'player'
players = [player.Player.random_player(n + str(i), 14, 14) for i in range(10)]

t = tournament.Tournament(players)
t.all_vs_all()

ranking = t.ranking()
top1, score_top1 = ranking[0]
top2, score_top2 = ranking[1]
print('\n\n\n\nGen 0 Top 2:')
print(top1.name, ':', score_top1['w'], 'ganadas	', score_top1['d'], 'empatadas	', score_top1['l'], 'perdidas')
print(top2.name, ':', score_top2['w'], 'ganadas	', score_top2['d'], 'empatadas	', score_top2['l'], 'perdidas')

# top1.save()
# top2.save()

for i in range(1, numGens):
	gen += 1
	print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
	print('X                         Generación {}                            X'.format(gen))
	print('XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX')
	
	n = 'gen' + str(gen) + 'player'
	players = player.Player.new_generation(gen, top1, top2, 10, 14, 14)

	t = tournament.Tournament(players)
	t.all_vs_all()

	ranking = t.ranking()
	top1, score_top1 = ranking[0]
	top2, score_top2 = ranking[1]
	print('\n\n\n\nGen {} Top 2:'.format(gen))
	print(top1.name, ':', score_top1['w'], 'ganadas	', score_top1['d'], 'empatadas	', score_top1['l'], 'perdidas')
	print(top2.name, ':', score_top2['w'], 'ganadas	', score_top2['d'], 'empatadas	', score_top2['l'], 'perdidas')

	# top1.save()
	# top2.save()
top1.save()
top2.save()