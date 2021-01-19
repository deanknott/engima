# Enigma Machine
This project emulates an enigma machine created my Alan Turing.

### Commands
In your terminal:
* run `erl`
* Then compile the program by running `c(enigma).`
* Create an enigma pid by running `PID = enigma:setup("B", {"III","I","II"}, {12,6,18},[{$A,$E},{$F,$J},{$P,$R}], {$D,$F,$R}).` You can change the variables as desired.
* Perform the encryption by running `enigma:crypt(PID,"String of text").`
