-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopeFineWords.lean: rows_ok of Johnson/Meaning/RopeWords.lean anew, from finer
pieces: the list recursion of Johnson/Meaning/RopeLists.lean at the stored example's numbers (cs 12,
theta0 500000, 64 pairs, 1024 tokens) gives, word for word, the entries of the library's stored
tables Data.cos and Data.sin; and no stored word passes 8192.

By 512 evaluations in Lean's kernel, one for each pair and each eighth of the tokens, each in a
module of its own (Johnson/Meaning/RopePart/R00Q0.lean to R63Q7.lean), some seconds and below 1 GB
of the process's own memory a module; they build side by side.
  row_fine_0 to row_fine_63: rowOK at each pair, by rowOK_of_parts (Johnson/Meaning/RopeFine.lean).
  rows_ok_fine: the statement of rows_ok, letter for letter.
-/
import Johnson.Meaning.RopePart.R00Q0
import Johnson.Meaning.RopePart.R00Q1
import Johnson.Meaning.RopePart.R00Q2
import Johnson.Meaning.RopePart.R00Q3
import Johnson.Meaning.RopePart.R00Q4
import Johnson.Meaning.RopePart.R00Q5
import Johnson.Meaning.RopePart.R00Q6
import Johnson.Meaning.RopePart.R00Q7
import Johnson.Meaning.RopePart.R01Q0
import Johnson.Meaning.RopePart.R01Q1
import Johnson.Meaning.RopePart.R01Q2
import Johnson.Meaning.RopePart.R01Q3
import Johnson.Meaning.RopePart.R01Q4
import Johnson.Meaning.RopePart.R01Q5
import Johnson.Meaning.RopePart.R01Q6
import Johnson.Meaning.RopePart.R01Q7
import Johnson.Meaning.RopePart.R02Q0
import Johnson.Meaning.RopePart.R02Q1
import Johnson.Meaning.RopePart.R02Q2
import Johnson.Meaning.RopePart.R02Q3
import Johnson.Meaning.RopePart.R02Q4
import Johnson.Meaning.RopePart.R02Q5
import Johnson.Meaning.RopePart.R02Q6
import Johnson.Meaning.RopePart.R02Q7
import Johnson.Meaning.RopePart.R03Q0
import Johnson.Meaning.RopePart.R03Q1
import Johnson.Meaning.RopePart.R03Q2
import Johnson.Meaning.RopePart.R03Q3
import Johnson.Meaning.RopePart.R03Q4
import Johnson.Meaning.RopePart.R03Q5
import Johnson.Meaning.RopePart.R03Q6
import Johnson.Meaning.RopePart.R03Q7
import Johnson.Meaning.RopePart.R04Q0
import Johnson.Meaning.RopePart.R04Q1
import Johnson.Meaning.RopePart.R04Q2
import Johnson.Meaning.RopePart.R04Q3
import Johnson.Meaning.RopePart.R04Q4
import Johnson.Meaning.RopePart.R04Q5
import Johnson.Meaning.RopePart.R04Q6
import Johnson.Meaning.RopePart.R04Q7
import Johnson.Meaning.RopePart.R05Q0
import Johnson.Meaning.RopePart.R05Q1
import Johnson.Meaning.RopePart.R05Q2
import Johnson.Meaning.RopePart.R05Q3
import Johnson.Meaning.RopePart.R05Q4
import Johnson.Meaning.RopePart.R05Q5
import Johnson.Meaning.RopePart.R05Q6
import Johnson.Meaning.RopePart.R05Q7
import Johnson.Meaning.RopePart.R06Q0
import Johnson.Meaning.RopePart.R06Q1
import Johnson.Meaning.RopePart.R06Q2
import Johnson.Meaning.RopePart.R06Q3
import Johnson.Meaning.RopePart.R06Q4
import Johnson.Meaning.RopePart.R06Q5
import Johnson.Meaning.RopePart.R06Q6
import Johnson.Meaning.RopePart.R06Q7
import Johnson.Meaning.RopePart.R07Q0
import Johnson.Meaning.RopePart.R07Q1
import Johnson.Meaning.RopePart.R07Q2
import Johnson.Meaning.RopePart.R07Q3
import Johnson.Meaning.RopePart.R07Q4
import Johnson.Meaning.RopePart.R07Q5
import Johnson.Meaning.RopePart.R07Q6
import Johnson.Meaning.RopePart.R07Q7
import Johnson.Meaning.RopePart.R08Q0
import Johnson.Meaning.RopePart.R08Q1
import Johnson.Meaning.RopePart.R08Q2
import Johnson.Meaning.RopePart.R08Q3
import Johnson.Meaning.RopePart.R08Q4
import Johnson.Meaning.RopePart.R08Q5
import Johnson.Meaning.RopePart.R08Q6
import Johnson.Meaning.RopePart.R08Q7
import Johnson.Meaning.RopePart.R09Q0
import Johnson.Meaning.RopePart.R09Q1
import Johnson.Meaning.RopePart.R09Q2
import Johnson.Meaning.RopePart.R09Q3
import Johnson.Meaning.RopePart.R09Q4
import Johnson.Meaning.RopePart.R09Q5
import Johnson.Meaning.RopePart.R09Q6
import Johnson.Meaning.RopePart.R09Q7
import Johnson.Meaning.RopePart.R10Q0
import Johnson.Meaning.RopePart.R10Q1
import Johnson.Meaning.RopePart.R10Q2
import Johnson.Meaning.RopePart.R10Q3
import Johnson.Meaning.RopePart.R10Q4
import Johnson.Meaning.RopePart.R10Q5
import Johnson.Meaning.RopePart.R10Q6
import Johnson.Meaning.RopePart.R10Q7
import Johnson.Meaning.RopePart.R11Q0
import Johnson.Meaning.RopePart.R11Q1
import Johnson.Meaning.RopePart.R11Q2
import Johnson.Meaning.RopePart.R11Q3
import Johnson.Meaning.RopePart.R11Q4
import Johnson.Meaning.RopePart.R11Q5
import Johnson.Meaning.RopePart.R11Q6
import Johnson.Meaning.RopePart.R11Q7
import Johnson.Meaning.RopePart.R12Q0
import Johnson.Meaning.RopePart.R12Q1
import Johnson.Meaning.RopePart.R12Q2
import Johnson.Meaning.RopePart.R12Q3
import Johnson.Meaning.RopePart.R12Q4
import Johnson.Meaning.RopePart.R12Q5
import Johnson.Meaning.RopePart.R12Q6
import Johnson.Meaning.RopePart.R12Q7
import Johnson.Meaning.RopePart.R13Q0
import Johnson.Meaning.RopePart.R13Q1
import Johnson.Meaning.RopePart.R13Q2
import Johnson.Meaning.RopePart.R13Q3
import Johnson.Meaning.RopePart.R13Q4
import Johnson.Meaning.RopePart.R13Q5
import Johnson.Meaning.RopePart.R13Q6
import Johnson.Meaning.RopePart.R13Q7
import Johnson.Meaning.RopePart.R14Q0
import Johnson.Meaning.RopePart.R14Q1
import Johnson.Meaning.RopePart.R14Q2
import Johnson.Meaning.RopePart.R14Q3
import Johnson.Meaning.RopePart.R14Q4
import Johnson.Meaning.RopePart.R14Q5
import Johnson.Meaning.RopePart.R14Q6
import Johnson.Meaning.RopePart.R14Q7
import Johnson.Meaning.RopePart.R15Q0
import Johnson.Meaning.RopePart.R15Q1
import Johnson.Meaning.RopePart.R15Q2
import Johnson.Meaning.RopePart.R15Q3
import Johnson.Meaning.RopePart.R15Q4
import Johnson.Meaning.RopePart.R15Q5
import Johnson.Meaning.RopePart.R15Q6
import Johnson.Meaning.RopePart.R15Q7
import Johnson.Meaning.RopePart.R16Q0
import Johnson.Meaning.RopePart.R16Q1
import Johnson.Meaning.RopePart.R16Q2
import Johnson.Meaning.RopePart.R16Q3
import Johnson.Meaning.RopePart.R16Q4
import Johnson.Meaning.RopePart.R16Q5
import Johnson.Meaning.RopePart.R16Q6
import Johnson.Meaning.RopePart.R16Q7
import Johnson.Meaning.RopePart.R17Q0
import Johnson.Meaning.RopePart.R17Q1
import Johnson.Meaning.RopePart.R17Q2
import Johnson.Meaning.RopePart.R17Q3
import Johnson.Meaning.RopePart.R17Q4
import Johnson.Meaning.RopePart.R17Q5
import Johnson.Meaning.RopePart.R17Q6
import Johnson.Meaning.RopePart.R17Q7
import Johnson.Meaning.RopePart.R18Q0
import Johnson.Meaning.RopePart.R18Q1
import Johnson.Meaning.RopePart.R18Q2
import Johnson.Meaning.RopePart.R18Q3
import Johnson.Meaning.RopePart.R18Q4
import Johnson.Meaning.RopePart.R18Q5
import Johnson.Meaning.RopePart.R18Q6
import Johnson.Meaning.RopePart.R18Q7
import Johnson.Meaning.RopePart.R19Q0
import Johnson.Meaning.RopePart.R19Q1
import Johnson.Meaning.RopePart.R19Q2
import Johnson.Meaning.RopePart.R19Q3
import Johnson.Meaning.RopePart.R19Q4
import Johnson.Meaning.RopePart.R19Q5
import Johnson.Meaning.RopePart.R19Q6
import Johnson.Meaning.RopePart.R19Q7
import Johnson.Meaning.RopePart.R20Q0
import Johnson.Meaning.RopePart.R20Q1
import Johnson.Meaning.RopePart.R20Q2
import Johnson.Meaning.RopePart.R20Q3
import Johnson.Meaning.RopePart.R20Q4
import Johnson.Meaning.RopePart.R20Q5
import Johnson.Meaning.RopePart.R20Q6
import Johnson.Meaning.RopePart.R20Q7
import Johnson.Meaning.RopePart.R21Q0
import Johnson.Meaning.RopePart.R21Q1
import Johnson.Meaning.RopePart.R21Q2
import Johnson.Meaning.RopePart.R21Q3
import Johnson.Meaning.RopePart.R21Q4
import Johnson.Meaning.RopePart.R21Q5
import Johnson.Meaning.RopePart.R21Q6
import Johnson.Meaning.RopePart.R21Q7
import Johnson.Meaning.RopePart.R22Q0
import Johnson.Meaning.RopePart.R22Q1
import Johnson.Meaning.RopePart.R22Q2
import Johnson.Meaning.RopePart.R22Q3
import Johnson.Meaning.RopePart.R22Q4
import Johnson.Meaning.RopePart.R22Q5
import Johnson.Meaning.RopePart.R22Q6
import Johnson.Meaning.RopePart.R22Q7
import Johnson.Meaning.RopePart.R23Q0
import Johnson.Meaning.RopePart.R23Q1
import Johnson.Meaning.RopePart.R23Q2
import Johnson.Meaning.RopePart.R23Q3
import Johnson.Meaning.RopePart.R23Q4
import Johnson.Meaning.RopePart.R23Q5
import Johnson.Meaning.RopePart.R23Q6
import Johnson.Meaning.RopePart.R23Q7
import Johnson.Meaning.RopePart.R24Q0
import Johnson.Meaning.RopePart.R24Q1
import Johnson.Meaning.RopePart.R24Q2
import Johnson.Meaning.RopePart.R24Q3
import Johnson.Meaning.RopePart.R24Q4
import Johnson.Meaning.RopePart.R24Q5
import Johnson.Meaning.RopePart.R24Q6
import Johnson.Meaning.RopePart.R24Q7
import Johnson.Meaning.RopePart.R25Q0
import Johnson.Meaning.RopePart.R25Q1
import Johnson.Meaning.RopePart.R25Q2
import Johnson.Meaning.RopePart.R25Q3
import Johnson.Meaning.RopePart.R25Q4
import Johnson.Meaning.RopePart.R25Q5
import Johnson.Meaning.RopePart.R25Q6
import Johnson.Meaning.RopePart.R25Q7
import Johnson.Meaning.RopePart.R26Q0
import Johnson.Meaning.RopePart.R26Q1
import Johnson.Meaning.RopePart.R26Q2
import Johnson.Meaning.RopePart.R26Q3
import Johnson.Meaning.RopePart.R26Q4
import Johnson.Meaning.RopePart.R26Q5
import Johnson.Meaning.RopePart.R26Q6
import Johnson.Meaning.RopePart.R26Q7
import Johnson.Meaning.RopePart.R27Q0
import Johnson.Meaning.RopePart.R27Q1
import Johnson.Meaning.RopePart.R27Q2
import Johnson.Meaning.RopePart.R27Q3
import Johnson.Meaning.RopePart.R27Q4
import Johnson.Meaning.RopePart.R27Q5
import Johnson.Meaning.RopePart.R27Q6
import Johnson.Meaning.RopePart.R27Q7
import Johnson.Meaning.RopePart.R28Q0
import Johnson.Meaning.RopePart.R28Q1
import Johnson.Meaning.RopePart.R28Q2
import Johnson.Meaning.RopePart.R28Q3
import Johnson.Meaning.RopePart.R28Q4
import Johnson.Meaning.RopePart.R28Q5
import Johnson.Meaning.RopePart.R28Q6
import Johnson.Meaning.RopePart.R28Q7
import Johnson.Meaning.RopePart.R29Q0
import Johnson.Meaning.RopePart.R29Q1
import Johnson.Meaning.RopePart.R29Q2
import Johnson.Meaning.RopePart.R29Q3
import Johnson.Meaning.RopePart.R29Q4
import Johnson.Meaning.RopePart.R29Q5
import Johnson.Meaning.RopePart.R29Q6
import Johnson.Meaning.RopePart.R29Q7
import Johnson.Meaning.RopePart.R30Q0
import Johnson.Meaning.RopePart.R30Q1
import Johnson.Meaning.RopePart.R30Q2
import Johnson.Meaning.RopePart.R30Q3
import Johnson.Meaning.RopePart.R30Q4
import Johnson.Meaning.RopePart.R30Q5
import Johnson.Meaning.RopePart.R30Q6
import Johnson.Meaning.RopePart.R30Q7
import Johnson.Meaning.RopePart.R31Q0
import Johnson.Meaning.RopePart.R31Q1
import Johnson.Meaning.RopePart.R31Q2
import Johnson.Meaning.RopePart.R31Q3
import Johnson.Meaning.RopePart.R31Q4
import Johnson.Meaning.RopePart.R31Q5
import Johnson.Meaning.RopePart.R31Q6
import Johnson.Meaning.RopePart.R31Q7
import Johnson.Meaning.RopePart.R32Q0
import Johnson.Meaning.RopePart.R32Q1
import Johnson.Meaning.RopePart.R32Q2
import Johnson.Meaning.RopePart.R32Q3
import Johnson.Meaning.RopePart.R32Q4
import Johnson.Meaning.RopePart.R32Q5
import Johnson.Meaning.RopePart.R32Q6
import Johnson.Meaning.RopePart.R32Q7
import Johnson.Meaning.RopePart.R33Q0
import Johnson.Meaning.RopePart.R33Q1
import Johnson.Meaning.RopePart.R33Q2
import Johnson.Meaning.RopePart.R33Q3
import Johnson.Meaning.RopePart.R33Q4
import Johnson.Meaning.RopePart.R33Q5
import Johnson.Meaning.RopePart.R33Q6
import Johnson.Meaning.RopePart.R33Q7
import Johnson.Meaning.RopePart.R34Q0
import Johnson.Meaning.RopePart.R34Q1
import Johnson.Meaning.RopePart.R34Q2
import Johnson.Meaning.RopePart.R34Q3
import Johnson.Meaning.RopePart.R34Q4
import Johnson.Meaning.RopePart.R34Q5
import Johnson.Meaning.RopePart.R34Q6
import Johnson.Meaning.RopePart.R34Q7
import Johnson.Meaning.RopePart.R35Q0
import Johnson.Meaning.RopePart.R35Q1
import Johnson.Meaning.RopePart.R35Q2
import Johnson.Meaning.RopePart.R35Q3
import Johnson.Meaning.RopePart.R35Q4
import Johnson.Meaning.RopePart.R35Q5
import Johnson.Meaning.RopePart.R35Q6
import Johnson.Meaning.RopePart.R35Q7
import Johnson.Meaning.RopePart.R36Q0
import Johnson.Meaning.RopePart.R36Q1
import Johnson.Meaning.RopePart.R36Q2
import Johnson.Meaning.RopePart.R36Q3
import Johnson.Meaning.RopePart.R36Q4
import Johnson.Meaning.RopePart.R36Q5
import Johnson.Meaning.RopePart.R36Q6
import Johnson.Meaning.RopePart.R36Q7
import Johnson.Meaning.RopePart.R37Q0
import Johnson.Meaning.RopePart.R37Q1
import Johnson.Meaning.RopePart.R37Q2
import Johnson.Meaning.RopePart.R37Q3
import Johnson.Meaning.RopePart.R37Q4
import Johnson.Meaning.RopePart.R37Q5
import Johnson.Meaning.RopePart.R37Q6
import Johnson.Meaning.RopePart.R37Q7
import Johnson.Meaning.RopePart.R38Q0
import Johnson.Meaning.RopePart.R38Q1
import Johnson.Meaning.RopePart.R38Q2
import Johnson.Meaning.RopePart.R38Q3
import Johnson.Meaning.RopePart.R38Q4
import Johnson.Meaning.RopePart.R38Q5
import Johnson.Meaning.RopePart.R38Q6
import Johnson.Meaning.RopePart.R38Q7
import Johnson.Meaning.RopePart.R39Q0
import Johnson.Meaning.RopePart.R39Q1
import Johnson.Meaning.RopePart.R39Q2
import Johnson.Meaning.RopePart.R39Q3
import Johnson.Meaning.RopePart.R39Q4
import Johnson.Meaning.RopePart.R39Q5
import Johnson.Meaning.RopePart.R39Q6
import Johnson.Meaning.RopePart.R39Q7
import Johnson.Meaning.RopePart.R40Q0
import Johnson.Meaning.RopePart.R40Q1
import Johnson.Meaning.RopePart.R40Q2
import Johnson.Meaning.RopePart.R40Q3
import Johnson.Meaning.RopePart.R40Q4
import Johnson.Meaning.RopePart.R40Q5
import Johnson.Meaning.RopePart.R40Q6
import Johnson.Meaning.RopePart.R40Q7
import Johnson.Meaning.RopePart.R41Q0
import Johnson.Meaning.RopePart.R41Q1
import Johnson.Meaning.RopePart.R41Q2
import Johnson.Meaning.RopePart.R41Q3
import Johnson.Meaning.RopePart.R41Q4
import Johnson.Meaning.RopePart.R41Q5
import Johnson.Meaning.RopePart.R41Q6
import Johnson.Meaning.RopePart.R41Q7
import Johnson.Meaning.RopePart.R42Q0
import Johnson.Meaning.RopePart.R42Q1
import Johnson.Meaning.RopePart.R42Q2
import Johnson.Meaning.RopePart.R42Q3
import Johnson.Meaning.RopePart.R42Q4
import Johnson.Meaning.RopePart.R42Q5
import Johnson.Meaning.RopePart.R42Q6
import Johnson.Meaning.RopePart.R42Q7
import Johnson.Meaning.RopePart.R43Q0
import Johnson.Meaning.RopePart.R43Q1
import Johnson.Meaning.RopePart.R43Q2
import Johnson.Meaning.RopePart.R43Q3
import Johnson.Meaning.RopePart.R43Q4
import Johnson.Meaning.RopePart.R43Q5
import Johnson.Meaning.RopePart.R43Q6
import Johnson.Meaning.RopePart.R43Q7
import Johnson.Meaning.RopePart.R44Q0
import Johnson.Meaning.RopePart.R44Q1
import Johnson.Meaning.RopePart.R44Q2
import Johnson.Meaning.RopePart.R44Q3
import Johnson.Meaning.RopePart.R44Q4
import Johnson.Meaning.RopePart.R44Q5
import Johnson.Meaning.RopePart.R44Q6
import Johnson.Meaning.RopePart.R44Q7
import Johnson.Meaning.RopePart.R45Q0
import Johnson.Meaning.RopePart.R45Q1
import Johnson.Meaning.RopePart.R45Q2
import Johnson.Meaning.RopePart.R45Q3
import Johnson.Meaning.RopePart.R45Q4
import Johnson.Meaning.RopePart.R45Q5
import Johnson.Meaning.RopePart.R45Q6
import Johnson.Meaning.RopePart.R45Q7
import Johnson.Meaning.RopePart.R46Q0
import Johnson.Meaning.RopePart.R46Q1
import Johnson.Meaning.RopePart.R46Q2
import Johnson.Meaning.RopePart.R46Q3
import Johnson.Meaning.RopePart.R46Q4
import Johnson.Meaning.RopePart.R46Q5
import Johnson.Meaning.RopePart.R46Q6
import Johnson.Meaning.RopePart.R46Q7
import Johnson.Meaning.RopePart.R47Q0
import Johnson.Meaning.RopePart.R47Q1
import Johnson.Meaning.RopePart.R47Q2
import Johnson.Meaning.RopePart.R47Q3
import Johnson.Meaning.RopePart.R47Q4
import Johnson.Meaning.RopePart.R47Q5
import Johnson.Meaning.RopePart.R47Q6
import Johnson.Meaning.RopePart.R47Q7
import Johnson.Meaning.RopePart.R48Q0
import Johnson.Meaning.RopePart.R48Q1
import Johnson.Meaning.RopePart.R48Q2
import Johnson.Meaning.RopePart.R48Q3
import Johnson.Meaning.RopePart.R48Q4
import Johnson.Meaning.RopePart.R48Q5
import Johnson.Meaning.RopePart.R48Q6
import Johnson.Meaning.RopePart.R48Q7
import Johnson.Meaning.RopePart.R49Q0
import Johnson.Meaning.RopePart.R49Q1
import Johnson.Meaning.RopePart.R49Q2
import Johnson.Meaning.RopePart.R49Q3
import Johnson.Meaning.RopePart.R49Q4
import Johnson.Meaning.RopePart.R49Q5
import Johnson.Meaning.RopePart.R49Q6
import Johnson.Meaning.RopePart.R49Q7
import Johnson.Meaning.RopePart.R50Q0
import Johnson.Meaning.RopePart.R50Q1
import Johnson.Meaning.RopePart.R50Q2
import Johnson.Meaning.RopePart.R50Q3
import Johnson.Meaning.RopePart.R50Q4
import Johnson.Meaning.RopePart.R50Q5
import Johnson.Meaning.RopePart.R50Q6
import Johnson.Meaning.RopePart.R50Q7
import Johnson.Meaning.RopePart.R51Q0
import Johnson.Meaning.RopePart.R51Q1
import Johnson.Meaning.RopePart.R51Q2
import Johnson.Meaning.RopePart.R51Q3
import Johnson.Meaning.RopePart.R51Q4
import Johnson.Meaning.RopePart.R51Q5
import Johnson.Meaning.RopePart.R51Q6
import Johnson.Meaning.RopePart.R51Q7
import Johnson.Meaning.RopePart.R52Q0
import Johnson.Meaning.RopePart.R52Q1
import Johnson.Meaning.RopePart.R52Q2
import Johnson.Meaning.RopePart.R52Q3
import Johnson.Meaning.RopePart.R52Q4
import Johnson.Meaning.RopePart.R52Q5
import Johnson.Meaning.RopePart.R52Q6
import Johnson.Meaning.RopePart.R52Q7
import Johnson.Meaning.RopePart.R53Q0
import Johnson.Meaning.RopePart.R53Q1
import Johnson.Meaning.RopePart.R53Q2
import Johnson.Meaning.RopePart.R53Q3
import Johnson.Meaning.RopePart.R53Q4
import Johnson.Meaning.RopePart.R53Q5
import Johnson.Meaning.RopePart.R53Q6
import Johnson.Meaning.RopePart.R53Q7
import Johnson.Meaning.RopePart.R54Q0
import Johnson.Meaning.RopePart.R54Q1
import Johnson.Meaning.RopePart.R54Q2
import Johnson.Meaning.RopePart.R54Q3
import Johnson.Meaning.RopePart.R54Q4
import Johnson.Meaning.RopePart.R54Q5
import Johnson.Meaning.RopePart.R54Q6
import Johnson.Meaning.RopePart.R54Q7
import Johnson.Meaning.RopePart.R55Q0
import Johnson.Meaning.RopePart.R55Q1
import Johnson.Meaning.RopePart.R55Q2
import Johnson.Meaning.RopePart.R55Q3
import Johnson.Meaning.RopePart.R55Q4
import Johnson.Meaning.RopePart.R55Q5
import Johnson.Meaning.RopePart.R55Q6
import Johnson.Meaning.RopePart.R55Q7
import Johnson.Meaning.RopePart.R56Q0
import Johnson.Meaning.RopePart.R56Q1
import Johnson.Meaning.RopePart.R56Q2
import Johnson.Meaning.RopePart.R56Q3
import Johnson.Meaning.RopePart.R56Q4
import Johnson.Meaning.RopePart.R56Q5
import Johnson.Meaning.RopePart.R56Q6
import Johnson.Meaning.RopePart.R56Q7
import Johnson.Meaning.RopePart.R57Q0
import Johnson.Meaning.RopePart.R57Q1
import Johnson.Meaning.RopePart.R57Q2
import Johnson.Meaning.RopePart.R57Q3
import Johnson.Meaning.RopePart.R57Q4
import Johnson.Meaning.RopePart.R57Q5
import Johnson.Meaning.RopePart.R57Q6
import Johnson.Meaning.RopePart.R57Q7
import Johnson.Meaning.RopePart.R58Q0
import Johnson.Meaning.RopePart.R58Q1
import Johnson.Meaning.RopePart.R58Q2
import Johnson.Meaning.RopePart.R58Q3
import Johnson.Meaning.RopePart.R58Q4
import Johnson.Meaning.RopePart.R58Q5
import Johnson.Meaning.RopePart.R58Q6
import Johnson.Meaning.RopePart.R58Q7
import Johnson.Meaning.RopePart.R59Q0
import Johnson.Meaning.RopePart.R59Q1
import Johnson.Meaning.RopePart.R59Q2
import Johnson.Meaning.RopePart.R59Q3
import Johnson.Meaning.RopePart.R59Q4
import Johnson.Meaning.RopePart.R59Q5
import Johnson.Meaning.RopePart.R59Q6
import Johnson.Meaning.RopePart.R59Q7
import Johnson.Meaning.RopePart.R60Q0
import Johnson.Meaning.RopePart.R60Q1
import Johnson.Meaning.RopePart.R60Q2
import Johnson.Meaning.RopePart.R60Q3
import Johnson.Meaning.RopePart.R60Q4
import Johnson.Meaning.RopePart.R60Q5
import Johnson.Meaning.RopePart.R60Q6
import Johnson.Meaning.RopePart.R60Q7
import Johnson.Meaning.RopePart.R61Q0
import Johnson.Meaning.RopePart.R61Q1
import Johnson.Meaning.RopePart.R61Q2
import Johnson.Meaning.RopePart.R61Q3
import Johnson.Meaning.RopePart.R61Q4
import Johnson.Meaning.RopePart.R61Q5
import Johnson.Meaning.RopePart.R61Q6
import Johnson.Meaning.RopePart.R61Q7
import Johnson.Meaning.RopePart.R62Q0
import Johnson.Meaning.RopePart.R62Q1
import Johnson.Meaning.RopePart.R62Q2
import Johnson.Meaning.RopePart.R62Q3
import Johnson.Meaning.RopePart.R62Q4
import Johnson.Meaning.RopePart.R62Q5
import Johnson.Meaning.RopePart.R62Q6
import Johnson.Meaning.RopePart.R62Q7
import Johnson.Meaning.RopePart.R63Q0
import Johnson.Meaning.RopePart.R63Q1
import Johnson.Meaning.RopePart.R63Q2
import Johnson.Meaning.RopePart.R63Q3
import Johnson.Meaning.RopePart.R63Q4
import Johnson.Meaning.RopePart.R63Q5
import Johnson.Meaning.RopePart.R63Q6
import Johnson.Meaning.RopePart.R63Q7

set_option autoImplicit false

namespace Meaning.Rope

theorem row_fine_0 : rowOK 0 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_0_0
    | 1, _ => part_0_1
    | 2, _ => part_0_2
    | 3, _ => part_0_3
    | 4, _ => part_0_4
    | 5, _ => part_0_5
    | 6, _ => part_0_6
    | 7, _ => part_0_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_1 : rowOK 1 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_1_0
    | 1, _ => part_1_1
    | 2, _ => part_1_2
    | 3, _ => part_1_3
    | 4, _ => part_1_4
    | 5, _ => part_1_5
    | 6, _ => part_1_6
    | 7, _ => part_1_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_2 : rowOK 2 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_2_0
    | 1, _ => part_2_1
    | 2, _ => part_2_2
    | 3, _ => part_2_3
    | 4, _ => part_2_4
    | 5, _ => part_2_5
    | 6, _ => part_2_6
    | 7, _ => part_2_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_3 : rowOK 3 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_3_0
    | 1, _ => part_3_1
    | 2, _ => part_3_2
    | 3, _ => part_3_3
    | 4, _ => part_3_4
    | 5, _ => part_3_5
    | 6, _ => part_3_6
    | 7, _ => part_3_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_4 : rowOK 4 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_4_0
    | 1, _ => part_4_1
    | 2, _ => part_4_2
    | 3, _ => part_4_3
    | 4, _ => part_4_4
    | 5, _ => part_4_5
    | 6, _ => part_4_6
    | 7, _ => part_4_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_5 : rowOK 5 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_5_0
    | 1, _ => part_5_1
    | 2, _ => part_5_2
    | 3, _ => part_5_3
    | 4, _ => part_5_4
    | 5, _ => part_5_5
    | 6, _ => part_5_6
    | 7, _ => part_5_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_6 : rowOK 6 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_6_0
    | 1, _ => part_6_1
    | 2, _ => part_6_2
    | 3, _ => part_6_3
    | 4, _ => part_6_4
    | 5, _ => part_6_5
    | 6, _ => part_6_6
    | 7, _ => part_6_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_7 : rowOK 7 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_7_0
    | 1, _ => part_7_1
    | 2, _ => part_7_2
    | 3, _ => part_7_3
    | 4, _ => part_7_4
    | 5, _ => part_7_5
    | 6, _ => part_7_6
    | 7, _ => part_7_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_8 : rowOK 8 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_8_0
    | 1, _ => part_8_1
    | 2, _ => part_8_2
    | 3, _ => part_8_3
    | 4, _ => part_8_4
    | 5, _ => part_8_5
    | 6, _ => part_8_6
    | 7, _ => part_8_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_9 : rowOK 9 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_9_0
    | 1, _ => part_9_1
    | 2, _ => part_9_2
    | 3, _ => part_9_3
    | 4, _ => part_9_4
    | 5, _ => part_9_5
    | 6, _ => part_9_6
    | 7, _ => part_9_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_10 : rowOK 10 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_10_0
    | 1, _ => part_10_1
    | 2, _ => part_10_2
    | 3, _ => part_10_3
    | 4, _ => part_10_4
    | 5, _ => part_10_5
    | 6, _ => part_10_6
    | 7, _ => part_10_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_11 : rowOK 11 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_11_0
    | 1, _ => part_11_1
    | 2, _ => part_11_2
    | 3, _ => part_11_3
    | 4, _ => part_11_4
    | 5, _ => part_11_5
    | 6, _ => part_11_6
    | 7, _ => part_11_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_12 : rowOK 12 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_12_0
    | 1, _ => part_12_1
    | 2, _ => part_12_2
    | 3, _ => part_12_3
    | 4, _ => part_12_4
    | 5, _ => part_12_5
    | 6, _ => part_12_6
    | 7, _ => part_12_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_13 : rowOK 13 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_13_0
    | 1, _ => part_13_1
    | 2, _ => part_13_2
    | 3, _ => part_13_3
    | 4, _ => part_13_4
    | 5, _ => part_13_5
    | 6, _ => part_13_6
    | 7, _ => part_13_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_14 : rowOK 14 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_14_0
    | 1, _ => part_14_1
    | 2, _ => part_14_2
    | 3, _ => part_14_3
    | 4, _ => part_14_4
    | 5, _ => part_14_5
    | 6, _ => part_14_6
    | 7, _ => part_14_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_15 : rowOK 15 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_15_0
    | 1, _ => part_15_1
    | 2, _ => part_15_2
    | 3, _ => part_15_3
    | 4, _ => part_15_4
    | 5, _ => part_15_5
    | 6, _ => part_15_6
    | 7, _ => part_15_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_16 : rowOK 16 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_16_0
    | 1, _ => part_16_1
    | 2, _ => part_16_2
    | 3, _ => part_16_3
    | 4, _ => part_16_4
    | 5, _ => part_16_5
    | 6, _ => part_16_6
    | 7, _ => part_16_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_17 : rowOK 17 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_17_0
    | 1, _ => part_17_1
    | 2, _ => part_17_2
    | 3, _ => part_17_3
    | 4, _ => part_17_4
    | 5, _ => part_17_5
    | 6, _ => part_17_6
    | 7, _ => part_17_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_18 : rowOK 18 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_18_0
    | 1, _ => part_18_1
    | 2, _ => part_18_2
    | 3, _ => part_18_3
    | 4, _ => part_18_4
    | 5, _ => part_18_5
    | 6, _ => part_18_6
    | 7, _ => part_18_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_19 : rowOK 19 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_19_0
    | 1, _ => part_19_1
    | 2, _ => part_19_2
    | 3, _ => part_19_3
    | 4, _ => part_19_4
    | 5, _ => part_19_5
    | 6, _ => part_19_6
    | 7, _ => part_19_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_20 : rowOK 20 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_20_0
    | 1, _ => part_20_1
    | 2, _ => part_20_2
    | 3, _ => part_20_3
    | 4, _ => part_20_4
    | 5, _ => part_20_5
    | 6, _ => part_20_6
    | 7, _ => part_20_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_21 : rowOK 21 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_21_0
    | 1, _ => part_21_1
    | 2, _ => part_21_2
    | 3, _ => part_21_3
    | 4, _ => part_21_4
    | 5, _ => part_21_5
    | 6, _ => part_21_6
    | 7, _ => part_21_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_22 : rowOK 22 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_22_0
    | 1, _ => part_22_1
    | 2, _ => part_22_2
    | 3, _ => part_22_3
    | 4, _ => part_22_4
    | 5, _ => part_22_5
    | 6, _ => part_22_6
    | 7, _ => part_22_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_23 : rowOK 23 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_23_0
    | 1, _ => part_23_1
    | 2, _ => part_23_2
    | 3, _ => part_23_3
    | 4, _ => part_23_4
    | 5, _ => part_23_5
    | 6, _ => part_23_6
    | 7, _ => part_23_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_24 : rowOK 24 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_24_0
    | 1, _ => part_24_1
    | 2, _ => part_24_2
    | 3, _ => part_24_3
    | 4, _ => part_24_4
    | 5, _ => part_24_5
    | 6, _ => part_24_6
    | 7, _ => part_24_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_25 : rowOK 25 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_25_0
    | 1, _ => part_25_1
    | 2, _ => part_25_2
    | 3, _ => part_25_3
    | 4, _ => part_25_4
    | 5, _ => part_25_5
    | 6, _ => part_25_6
    | 7, _ => part_25_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_26 : rowOK 26 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_26_0
    | 1, _ => part_26_1
    | 2, _ => part_26_2
    | 3, _ => part_26_3
    | 4, _ => part_26_4
    | 5, _ => part_26_5
    | 6, _ => part_26_6
    | 7, _ => part_26_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_27 : rowOK 27 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_27_0
    | 1, _ => part_27_1
    | 2, _ => part_27_2
    | 3, _ => part_27_3
    | 4, _ => part_27_4
    | 5, _ => part_27_5
    | 6, _ => part_27_6
    | 7, _ => part_27_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_28 : rowOK 28 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_28_0
    | 1, _ => part_28_1
    | 2, _ => part_28_2
    | 3, _ => part_28_3
    | 4, _ => part_28_4
    | 5, _ => part_28_5
    | 6, _ => part_28_6
    | 7, _ => part_28_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_29 : rowOK 29 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_29_0
    | 1, _ => part_29_1
    | 2, _ => part_29_2
    | 3, _ => part_29_3
    | 4, _ => part_29_4
    | 5, _ => part_29_5
    | 6, _ => part_29_6
    | 7, _ => part_29_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_30 : rowOK 30 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_30_0
    | 1, _ => part_30_1
    | 2, _ => part_30_2
    | 3, _ => part_30_3
    | 4, _ => part_30_4
    | 5, _ => part_30_5
    | 6, _ => part_30_6
    | 7, _ => part_30_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_31 : rowOK 31 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_31_0
    | 1, _ => part_31_1
    | 2, _ => part_31_2
    | 3, _ => part_31_3
    | 4, _ => part_31_4
    | 5, _ => part_31_5
    | 6, _ => part_31_6
    | 7, _ => part_31_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_32 : rowOK 32 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_32_0
    | 1, _ => part_32_1
    | 2, _ => part_32_2
    | 3, _ => part_32_3
    | 4, _ => part_32_4
    | 5, _ => part_32_5
    | 6, _ => part_32_6
    | 7, _ => part_32_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_33 : rowOK 33 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_33_0
    | 1, _ => part_33_1
    | 2, _ => part_33_2
    | 3, _ => part_33_3
    | 4, _ => part_33_4
    | 5, _ => part_33_5
    | 6, _ => part_33_6
    | 7, _ => part_33_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_34 : rowOK 34 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_34_0
    | 1, _ => part_34_1
    | 2, _ => part_34_2
    | 3, _ => part_34_3
    | 4, _ => part_34_4
    | 5, _ => part_34_5
    | 6, _ => part_34_6
    | 7, _ => part_34_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_35 : rowOK 35 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_35_0
    | 1, _ => part_35_1
    | 2, _ => part_35_2
    | 3, _ => part_35_3
    | 4, _ => part_35_4
    | 5, _ => part_35_5
    | 6, _ => part_35_6
    | 7, _ => part_35_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_36 : rowOK 36 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_36_0
    | 1, _ => part_36_1
    | 2, _ => part_36_2
    | 3, _ => part_36_3
    | 4, _ => part_36_4
    | 5, _ => part_36_5
    | 6, _ => part_36_6
    | 7, _ => part_36_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_37 : rowOK 37 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_37_0
    | 1, _ => part_37_1
    | 2, _ => part_37_2
    | 3, _ => part_37_3
    | 4, _ => part_37_4
    | 5, _ => part_37_5
    | 6, _ => part_37_6
    | 7, _ => part_37_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_38 : rowOK 38 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_38_0
    | 1, _ => part_38_1
    | 2, _ => part_38_2
    | 3, _ => part_38_3
    | 4, _ => part_38_4
    | 5, _ => part_38_5
    | 6, _ => part_38_6
    | 7, _ => part_38_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_39 : rowOK 39 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_39_0
    | 1, _ => part_39_1
    | 2, _ => part_39_2
    | 3, _ => part_39_3
    | 4, _ => part_39_4
    | 5, _ => part_39_5
    | 6, _ => part_39_6
    | 7, _ => part_39_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_40 : rowOK 40 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_40_0
    | 1, _ => part_40_1
    | 2, _ => part_40_2
    | 3, _ => part_40_3
    | 4, _ => part_40_4
    | 5, _ => part_40_5
    | 6, _ => part_40_6
    | 7, _ => part_40_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_41 : rowOK 41 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_41_0
    | 1, _ => part_41_1
    | 2, _ => part_41_2
    | 3, _ => part_41_3
    | 4, _ => part_41_4
    | 5, _ => part_41_5
    | 6, _ => part_41_6
    | 7, _ => part_41_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_42 : rowOK 42 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_42_0
    | 1, _ => part_42_1
    | 2, _ => part_42_2
    | 3, _ => part_42_3
    | 4, _ => part_42_4
    | 5, _ => part_42_5
    | 6, _ => part_42_6
    | 7, _ => part_42_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_43 : rowOK 43 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_43_0
    | 1, _ => part_43_1
    | 2, _ => part_43_2
    | 3, _ => part_43_3
    | 4, _ => part_43_4
    | 5, _ => part_43_5
    | 6, _ => part_43_6
    | 7, _ => part_43_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_44 : rowOK 44 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_44_0
    | 1, _ => part_44_1
    | 2, _ => part_44_2
    | 3, _ => part_44_3
    | 4, _ => part_44_4
    | 5, _ => part_44_5
    | 6, _ => part_44_6
    | 7, _ => part_44_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_45 : rowOK 45 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_45_0
    | 1, _ => part_45_1
    | 2, _ => part_45_2
    | 3, _ => part_45_3
    | 4, _ => part_45_4
    | 5, _ => part_45_5
    | 6, _ => part_45_6
    | 7, _ => part_45_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_46 : rowOK 46 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_46_0
    | 1, _ => part_46_1
    | 2, _ => part_46_2
    | 3, _ => part_46_3
    | 4, _ => part_46_4
    | 5, _ => part_46_5
    | 6, _ => part_46_6
    | 7, _ => part_46_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_47 : rowOK 47 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_47_0
    | 1, _ => part_47_1
    | 2, _ => part_47_2
    | 3, _ => part_47_3
    | 4, _ => part_47_4
    | 5, _ => part_47_5
    | 6, _ => part_47_6
    | 7, _ => part_47_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_48 : rowOK 48 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_48_0
    | 1, _ => part_48_1
    | 2, _ => part_48_2
    | 3, _ => part_48_3
    | 4, _ => part_48_4
    | 5, _ => part_48_5
    | 6, _ => part_48_6
    | 7, _ => part_48_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_49 : rowOK 49 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_49_0
    | 1, _ => part_49_1
    | 2, _ => part_49_2
    | 3, _ => part_49_3
    | 4, _ => part_49_4
    | 5, _ => part_49_5
    | 6, _ => part_49_6
    | 7, _ => part_49_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_50 : rowOK 50 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_50_0
    | 1, _ => part_50_1
    | 2, _ => part_50_2
    | 3, _ => part_50_3
    | 4, _ => part_50_4
    | 5, _ => part_50_5
    | 6, _ => part_50_6
    | 7, _ => part_50_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_51 : rowOK 51 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_51_0
    | 1, _ => part_51_1
    | 2, _ => part_51_2
    | 3, _ => part_51_3
    | 4, _ => part_51_4
    | 5, _ => part_51_5
    | 6, _ => part_51_6
    | 7, _ => part_51_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_52 : rowOK 52 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_52_0
    | 1, _ => part_52_1
    | 2, _ => part_52_2
    | 3, _ => part_52_3
    | 4, _ => part_52_4
    | 5, _ => part_52_5
    | 6, _ => part_52_6
    | 7, _ => part_52_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_53 : rowOK 53 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_53_0
    | 1, _ => part_53_1
    | 2, _ => part_53_2
    | 3, _ => part_53_3
    | 4, _ => part_53_4
    | 5, _ => part_53_5
    | 6, _ => part_53_6
    | 7, _ => part_53_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_54 : rowOK 54 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_54_0
    | 1, _ => part_54_1
    | 2, _ => part_54_2
    | 3, _ => part_54_3
    | 4, _ => part_54_4
    | 5, _ => part_54_5
    | 6, _ => part_54_6
    | 7, _ => part_54_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_55 : rowOK 55 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_55_0
    | 1, _ => part_55_1
    | 2, _ => part_55_2
    | 3, _ => part_55_3
    | 4, _ => part_55_4
    | 5, _ => part_55_5
    | 6, _ => part_55_6
    | 7, _ => part_55_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_56 : rowOK 56 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_56_0
    | 1, _ => part_56_1
    | 2, _ => part_56_2
    | 3, _ => part_56_3
    | 4, _ => part_56_4
    | 5, _ => part_56_5
    | 6, _ => part_56_6
    | 7, _ => part_56_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_57 : rowOK 57 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_57_0
    | 1, _ => part_57_1
    | 2, _ => part_57_2
    | 3, _ => part_57_3
    | 4, _ => part_57_4
    | 5, _ => part_57_5
    | 6, _ => part_57_6
    | 7, _ => part_57_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_58 : rowOK 58 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_58_0
    | 1, _ => part_58_1
    | 2, _ => part_58_2
    | 3, _ => part_58_3
    | 4, _ => part_58_4
    | 5, _ => part_58_5
    | 6, _ => part_58_6
    | 7, _ => part_58_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_59 : rowOK 59 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_59_0
    | 1, _ => part_59_1
    | 2, _ => part_59_2
    | 3, _ => part_59_3
    | 4, _ => part_59_4
    | 5, _ => part_59_5
    | 6, _ => part_59_6
    | 7, _ => part_59_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_60 : rowOK 60 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_60_0
    | 1, _ => part_60_1
    | 2, _ => part_60_2
    | 3, _ => part_60_3
    | 4, _ => part_60_4
    | 5, _ => part_60_5
    | 6, _ => part_60_6
    | 7, _ => part_60_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_61 : rowOK 61 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_61_0
    | 1, _ => part_61_1
    | 2, _ => part_61_2
    | 3, _ => part_61_3
    | 4, _ => part_61_4
    | 5, _ => part_61_5
    | 6, _ => part_61_6
    | 7, _ => part_61_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_62 : rowOK 62 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_62_0
    | 1, _ => part_62_1
    | 2, _ => part_62_2
    | 3, _ => part_62_3
    | 4, _ => part_62_4
    | 5, _ => part_62_5
    | 6, _ => part_62_6
    | 7, _ => part_62_7
    | n + 8, h => absurd h (by omega)

theorem row_fine_63 : rowOK 63 = true :=
  rowOK_of_parts fun q hq =>
    match q, hq with
    | 0, _ => part_63_0
    | 1, _ => part_63_1
    | 2, _ => part_63_2
    | 3, _ => part_63_3
    | 4, _ => part_63_4
    | 5, _ => part_63_5
    | 6, _ => part_63_6
    | 7, _ => part_63_7
    | n + 8, h => absurd h (by omega)

/-- The test holds at every pair. -/
theorem rows_ok_fine : ∀ i, i < 64 → rowOK i = true
  | 0, _ => row_fine_0
  | 1, _ => row_fine_1
  | 2, _ => row_fine_2
  | 3, _ => row_fine_3
  | 4, _ => row_fine_4
  | 5, _ => row_fine_5
  | 6, _ => row_fine_6
  | 7, _ => row_fine_7
  | 8, _ => row_fine_8
  | 9, _ => row_fine_9
  | 10, _ => row_fine_10
  | 11, _ => row_fine_11
  | 12, _ => row_fine_12
  | 13, _ => row_fine_13
  | 14, _ => row_fine_14
  | 15, _ => row_fine_15
  | 16, _ => row_fine_16
  | 17, _ => row_fine_17
  | 18, _ => row_fine_18
  | 19, _ => row_fine_19
  | 20, _ => row_fine_20
  | 21, _ => row_fine_21
  | 22, _ => row_fine_22
  | 23, _ => row_fine_23
  | 24, _ => row_fine_24
  | 25, _ => row_fine_25
  | 26, _ => row_fine_26
  | 27, _ => row_fine_27
  | 28, _ => row_fine_28
  | 29, _ => row_fine_29
  | 30, _ => row_fine_30
  | 31, _ => row_fine_31
  | 32, _ => row_fine_32
  | 33, _ => row_fine_33
  | 34, _ => row_fine_34
  | 35, _ => row_fine_35
  | 36, _ => row_fine_36
  | 37, _ => row_fine_37
  | 38, _ => row_fine_38
  | 39, _ => row_fine_39
  | 40, _ => row_fine_40
  | 41, _ => row_fine_41
  | 42, _ => row_fine_42
  | 43, _ => row_fine_43
  | 44, _ => row_fine_44
  | 45, _ => row_fine_45
  | 46, _ => row_fine_46
  | 47, _ => row_fine_47
  | 48, _ => row_fine_48
  | 49, _ => row_fine_49
  | 50, _ => row_fine_50
  | 51, _ => row_fine_51
  | 52, _ => row_fine_52
  | 53, _ => row_fine_53
  | 54, _ => row_fine_54
  | 55, _ => row_fine_55
  | 56, _ => row_fine_56
  | 57, _ => row_fine_57
  | 58, _ => row_fine_58
  | 59, _ => row_fine_59
  | 60, _ => row_fine_60
  | 61, _ => row_fine_61
  | 62, _ => row_fine_62
  | 63, _ => row_fine_63
  | n + 64, h => absurd h (by omega)

#print axioms rows_ok_fine

end Meaning.Rope
