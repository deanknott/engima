% Author Dean Knott.
% The enigma module is a system that implements Enigma machine processes.
% Several processes are used within this implementation that take the role of
% different enigma proccesses such as the keyboard, plugboard, rotors, and reflector.
-module(enigma).
-export([setup/5, crypt/2, kill/1]).
-include("enigma.hrl").

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Exported functions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Creates a new Enigma process consisting of a reflector name,
% triple of rotor names, a triple of ring-settings, a list of plugboard pairs,
% and an initial setting, and returns a PID of an Enigma machine
setup(ReflectorName, RotorNames, RingSettings, PlugboardPairs, InitialSettings) ->
  spawn(fun() ->
    enigma(ReflectorName, RotorNames, RingSettings, PlugboardPairs, InitialSettings) end).


% Handles all communication within the machine. It uses a PID of an Enigma
% machine (produced by setup/5), and a string of text to be passed through the machine
% The message is converted to uppercase so a is treated as A etc.
crypt(_EnigmaPID, _Message = []) ->
  "";
crypt(EnigmaPID, [H | T]) ->
  EnigmaPID ! build_message({input, string:to_upper(H)}),
  receive
    {EnigmaPID, {output, Char}} ->
      [Char | crypt(EnigmaPID, string:uppercase(T))]
  end.

%% Shuts down the Enigma machine, terminating all processes.
kill(EnigmaPID) ->
  exit(EnigmaPID, terminate_processes).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Extra functions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Calculates the turnover of a character for each rotor
turnover(Characters) ->
    lists:map(fun(Char) -> Char - 65 end, Characters).

% Returns the rotors and turnovers used in setup based on user input.
get_rotor(Name) ->
    case string:lowercase(Name) of
        "i" -> {lists:map(fun({_,V}) -> V end, rotorI()),turnover([$Q])};
        "ii" -> {lists:map(fun({_,V}) -> V end,rotorII()), turnover([$E])};
        "iii" -> {lists:map(fun({_,V}) -> V end,rotorIII()), turnover([$V])};
        "iv" -> {lists:map(fun({_,V}) -> V end,rotorIV()), turnover([$J])};
        "v" -> {lists:map(fun({_,V}) -> V end,rotorV()), turnover([$Z])};
        "vi" -> {lists:map(fun({_,V}) -> V end,rotorVI()), turnover([$Z, $M])};
        "vii" -> {lists:map(fun({_,V}) -> V end,rotorVII()), turnover([$Z, $M])};
        "viii" -> {lists:map(fun({_,V}) -> V end,rotorVIII()), turnover([$Z, $M])};
        "beta" -> {lists:map(fun({_,V}) -> V end,rotorBeta()), turnover([])};
        "gamma" -> {lists:map(fun({_,V}) -> V end,rotorGamma()), turnover([])}
    end.

% Returns the reflectors used in setup based on user input
get_reflector(Name) ->
    case string:lowercase(Name) of
        "a" -> reflectorA();
        "b" -> reflectorB();
        "c" -> reflectorC();
        "thinb" -> reflectorThinB();
        "thinc" -> reflectorThinC()
    end.


% Checks for an atom registered under a process.
isatom(PID) ->
    proplists:get_value(registered_name, erlang:process_info(PID)).

% Creates a tuple of an atom of the registered process and the data.
build_message(Data) ->
  Atom = isatom(self()),
  Process = case Atom of
    undefined -> self();
    _ -> Atom
  end,
  {Process, Data}.

% Returns the index of which an ASCII character is represented as in the alphabet
% ASCII range is 65 to 90
ascii_to_alphabet_position(AsciiCharacter) when AsciiCharacter >= 65 andalso AsciiCharacter =< 90 ->
  AsciiCharacter - 65;
ascii_to_alphabet_position(_) ->
  erlang:error(ascii_to_alphabet_position_out_of_range).


% Returns an index of the alphabet of which an ASCII character represents
% Alphabet range is 0 to 25
alphabet_to_ascii(AlphaPosition) when AlphaPosition >= 0 andalso AlphaPosition =< 25 ->
  AlphaPosition + 65;
alphabet_to_ascii(_) ->
  erlang:error(alphabet_to_ascii_out_of_range).

% Takes an input on channel in and reflects it out on channel out
reflector(Channels = #{in := In, out := Out}, Pairs) ->
  _ = receive
    {In, {char, Char}} ->
      Out ! build_message({char, f_refl_f_plug(Pairs, Char)})
  end,
  reflector(Channels, Pairs).

% Outputs a keypress on channel key and outputs an increment signal on channel
% inc to advance the rotors, and the waits for a signal on channel lamp to
% represent the result from the encryption process being received on the lamp board.
keyboard(Channels = #{key := Key, lamp := Lamp, inc := Increment}) ->
  receive
    {From, {char, InputChar}} ->
      keyboard_increment(Increment),
      Key ! build_message({char, InputChar}),
      receive
        {Lamp, DataOut = {char, _OutputChar}} ->
          From ! build_message(DataOut),
          keyboard(Channels)
      end
  end.

% Processes the keyboard increment signal
keyboard_increment(Increment) ->
  Increment ! build_message({inc}),
  receive
    {_From, {inc}} ->
      ok
  end.

% Passes messages from l to r or r to l via the f_refl_f_plug function
plugboard(Channels = #{l := Left, r := Right}, Pairs) ->
  _ = receive
    {Left, {char, Char}} ->
      Right ! build_message({char, f_refl_f_plug(Pairs, Char)});
    {Right, {char, Char}} ->
      Left ! build_message({char, f_refl_f_plug(Pairs, Char)})
  end,
  plugboard(Channels, Pairs).

% Used by the reflector and the plugboard to swap characters.
% Incorporated into one function as they run the same process
f_refl_f_plug(Pairs, Character) ->
  Result = proplists:get_value(Character, Pairs, Character),
  proplists:get_value(Character, lists:map(fun({A,B}) -> {B,A} end, Pairs), Result).

% Takes the modulo of two numbers.
mod(X, Y) when X > 0 -> X rem Y;
mod(X, Y) when X < 0 -> mod(X + Y, Y);
mod(0, _) -> 0.

% Accepts a character on the left channel, l, and output on channel r with the
% character modified by the rotor function.
rotor(Channels = #{l := LP, r := RP, inc_l := IncLP, inc_r := IncRP, inc_end := IncEnd},
  Rotor = {_, Turnovers}, Offset, RingSetting) ->
  receive
    {RP, {char, Char}} ->
      LP ! build_message({char, f_rotor(Rotor, Offset, RingSetting, Char)}),
      rotor(Channels, Rotor, Offset, RingSetting);
    {LP, {char, Char}} ->
      RP ! build_message({char, inverse_f_rotor(Rotor, Offset, RingSetting, Char)}),
      rotor(Channels, Rotor, Offset, RingSetting);
    {IncRP, Data = {inc}} ->
      _ = case lists:member(Offset, Turnovers) of
        true ->
          IncLP ! build_message(Data);
        _ ->
          IncEnd ! build_message(Data)
      end,
      rotor(Channels, Rotor, mod(Offset + 1, 26), RingSetting)
  end.

% Returns the rotor entry position using the offset
get_rotor_entry_position(Character, Offset, RingSetting) ->
  mod(ascii_to_alphabet_position(Character) + Offset - RingSetting, 26).


% Calculates the forward encoded output of the rotor i.e. right to left
f_rotor(_Rotor = {Message, _}, Offset, RingSetting, Character) ->
  Position = get_rotor_entry_position(Character, Offset, RingSetting),
  Encoded = encode(Message, Position),
  alphabet_to_ascii(mod(Encoded - Offset + RingSetting, 26)).


% Calculates the reverse encoded output of the rotor i.e. left to right
inverse_f_rotor(_Rotor = {Message, _}, Offset, RingSetting, Character) ->
  Position = get_rotor_entry_position(Character, Offset, RingSetting),
  Decoded = decode(Message, Position),
  alphabet_to_ascii(mod(Decoded - Offset + RingSetting, 26)).

% Encodes a particular index within the data Message.
encode(Message, Position) when length(Message) =:= 26 andalso Position >= 0 andalso Position < 26 ->
  ascii_to_alphabet_position(lists:nth(Position + 1, Message));
encode(Message, _) when length(Message) =:= 26 ->
  erlang:error(position_invalid);
encode(_, _) ->
  erlang:error(message_invalid).


% Decodes the character at a particular index within the Message
decode(Message, Position) ->
  string:chr(Message, alphabet_to_ascii(Position)) - 1.

% Generates the Enigma machine processes, loops the processes until terminated
enigma(ReflectorName, _RotorNames = {RL, RM, RR}, _RingSettings = {RS_L, RS_M, RS_R},
       PlugboardPairs, _Offsets = {Offset_L, Offset_M, Offset_R}) ->
  % Using spawn_link ensures the processes exit when enigma exits.
  register(reflector, spawn_link(fun() -> reflector(
    #{in => rl, out => rl},
    get_reflector(ReflectorName)) end)),
  register(rl, spawn_link(fun() -> rotor(
    #{l => reflector, r => rm, inc_l => keyboard, inc_r => rm, inc_end => keyboard},
    get_rotor(RL), ascii_to_alphabet_position(Offset_L), RS_L) end)),
  register(rm, spawn_link(fun() -> rotor(
    #{l => rl, r => rr, inc_l => rl, inc_r => rr, inc_end => keyboard},
    get_rotor(RM), ascii_to_alphabet_position(Offset_M), RS_M) end)),
  register(rr, spawn_link(fun() -> rotor(
    #{l => rm, r => plugboard, inc_l => rm, inc_r => keyboard, inc_end => keyboard},
    get_rotor(RR), ascii_to_alphabet_position(Offset_R), RS_R) end)),
  register(plugboard, spawn_link(fun() -> plugboard(
    #{l => rr, r => keyboard},
    PlugboardPairs) end)),
  register(keyboard, spawn_link(fun() -> keyboard(
    #{key => plugboard, lamp => plugboard, inc => rr}) end)),

  loop().


% Loops the enigma process communication with the keyboard
% 65 = A, 90 Z
loop() ->
  _ = receive
    {From, {input, InputChar}} when InputChar >= 65 andalso InputChar =< 90 ->
      keyboard ! build_message({char, InputChar}),
      receive
        {_Keyboard, {char, OutputChar}} ->
          From ! build_message({output, OutputChar})
      end;
    {From, {input, InputChar}} ->
      From ! build_message({output, InputChar})
  end,
  loop().
