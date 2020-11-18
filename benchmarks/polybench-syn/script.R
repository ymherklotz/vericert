library("psych")

data = read.csv("poly.csv", header=TRUE)
leguptime = (data$legupcycles/data$legupfreqMHz)
veritime = data$vericertcycles/data$vericertfreqMHz
print(lm(veritime ~ leguptime))
leguputil = data$leguplogicutilisation/427200*100
veriutil = data$vericertlogicutilisation/427200*100
print(lm (veriutil ~ leguputil))
legupct = data$legupcomptime
verict = data$vericertcomptime
print(lm ( verict ~ legupct ))

cycleslowdown=data$vericertcycles/data$legupcycles

print("Cycle count slow down")
print(geometric.mean(cycleslowdown))
print("Wall clock slow down")
print(geometric.mean(veritime/leguptime))
print("Area overhead")
print(geometric.mean(veriutil/leguputil))
print("Compilation time speedup")
print(geometric.mean(legupct/verict))
