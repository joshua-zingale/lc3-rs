# LC-3

LC-3 ("Little Computer 3") is a simple computer processor architecture designed for pedagogy.


This implementation of LC-3 follows the specification in "Introduction to Computing Systems 3rd Edition" by Yale Patt and Sanjay Patel.
The primary references from within the text are

- 9.2.2 Input from the Keyboard,
- 9.2.3 Output to the Monitor, and
- Appendix A.

Additionally, the primary references for the assembler are

- 7.2 An Assembly Language Program
- Appendix A

and inspired, but not in full agreement with, [LC3Tools](https://github.com/chiragsakhuja/lc3tools/tree/master).
Where LC3Tools is more liberal in its handling of labels during assembly,
this assembler follows the referenced text with respect to permitted characters and maximum length.
Also, LC3Tools permits multiple labels per instruction but this allows only one per instruction.
