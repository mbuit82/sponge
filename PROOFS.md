# Syntax for writing proofs
- first line must be the goal line, and must have "|-" before the goal (note the space there, and in following requirements).
- The proof is delimited by a header that is a line that only contains the word "Proof" on it
- You say you want to do deduction by having lines that say "deduction" between the theorem statement and the Proof header; the number of lines with "deduction" is the number of deductions you do
- proof lines must look like: "{lineNumber}. |-{ANY AMOUNT OF SPACE}{content}{ANY AMOUNT OF SPACE}by {JUSTIFICATIONSTUFF}: {REFSTUFF}" 
where the colon and {REFSTUFF} is optional (like depends on the justification).
- For citing/applying proofs, the justification looks like this: "by {VERB} {PROOFNAME} (from {LOGICNAME})" where {VERB} can be any of "citing", "using", or "applying", {PROOFNAME} is the name of the file of the proof you're citing and {LOGICNAME} is the name of the logic that proof is in. If you want to apply a theorem to previous lines (i.e. basically use it as a derived rule), then you add the colon and the line references after the colon
- currently, you must fully parenthesize, except that you can drop top level parentheses. You can put any amount of space between things, and unary operators don't need parentheses around their argument


see the example proofs to get a better idea. 
