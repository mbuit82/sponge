# Proof rules
- first line must be the goal line, and must have "|-" before the goal (note the space there, and in following requirements).
- you say you want to do deduction by having lines that say "deduction"; the number of lines with that is the number of deductions you do
- proof lines must have, as an f-string: 
f"{lineNumber}. |-{ANY AMOUNT OF SPACE}{content}{ANY AMOUNT OF SPACE}by {JUSTIFICATIONSTUFF},{REFSTUFF}" 
where the comma and {REFSTUFF} is optional (like depends on the justification)
- currently, only full parenthetization is supported, though you can drop top level parentheses. 


see the example proofs to get a better idea. 