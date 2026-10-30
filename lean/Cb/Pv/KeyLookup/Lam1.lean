-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Lam1.lean: THE LOOKUP WITH PARTS AS ONE CONSTANT, put together from its stretches;
and that it is knowledge
sound from «every key of every part is a row of the table» to «a claim a part, and the rows».

It imports the library's side alone (no file of the port): Cb/Pv/KeyLookup/Asm.lean and the
stretches:
  head (draw, fused tie) Cb/Pv/KeyLookup/TieM.lean      A.headK         parts' steps
  Cb/Pv/KeyLookup/PartsK.lean   A.partsXK
  join point Cb/Pv/KeyLookup/Join.lean      A.joinK         key sides, table
  Cb/Pv/KeyLookup/LevFit.lean   A.keysK, A.tableK
  closing Cb/Pv/KeyLookup/Close.lean     A.closeK        zero point, bits
  Cb/Pv/KeyLookup/Bits.lean     A.zeroK, A.bitsK.

  `Pl A`          where all own mask entries stand: the four stretches' records of places, side by
                  side. Letters.
  `A.bks P SK`    the eight blocks; SK: the sumcheck as a letter (a verifier and its errors:
                  `PscLtK`).
  `A.lam1 P SK`   THE LOOKUP: the eight in a row, then the read-out.
  `A.Lt P SK …`   what is asked of the letter: `Know` at each sumcheck that the lookup lays (tie,
                  parts, keys, table, closing, bits).
  `lam1_know`     UNDER `A.toPub.Adm p` AND `A.Lt P SK …`: `Know` of `A.lam1 P SK` between the same
                  joints, for EVERY letter SK.
  `lam1_know_lib` at the library's own sumcheck (`PscLtK.lib`): UNDER `A.toPub.Adm p` (p the
      characteristic), conditions on public numbers and
                  shapes, and nothing else: `Know` between the library-kind joints `A.jtIn` and
                  `A.jtOut`, beside EVERY riding joint R0, for every Mu.
No premise reads a witness or names an honest prover.
Know: for each fixed tuple of messages; the identity extracts; the errors are counts, unbounded
here. Mu is idle in Know. No value of A.Lt is written in this library; its six fields are proved one
by one at PscLtK.lib and at SK₀.
Not claimed: an honest side; anything on masks' places being apart; the list of errors
(Cb/Pv/KeyLookup/Lam1Short.lean).

-/
import Cb.Pv.KeyLookup.Asm
import Cb.Pv.KeyLookup.TieM
import Cb.Pv.KeyLookup.PartsK
import Cb.Pv.KeyLookup.LevFit
import Cb.Pv.KeyLookup.CloseLam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn

noncomputable section
variable {E : Type} [Field E] [Fintype E]

/-- Where all own mask entries stand. -/
structure Pl (A : Dat E) where
  tie : TiePl E A.J
  wP  : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J
  cP  : ℕ → Bool → A.J
  lev : LevPl A
  cl  : ClPl A

namespace Dat
variable (A : Dat E) (P : Pl A) {Ex : ExtSpec}

/-- The eight stretches that have rounds. -/
def bks (SK : PscLtK E Ex) : Bks A Ex where
  head  := A.headK P.tie SK (A.pl - 2)
  parts := A.partsXK P.wP P.cP SK
  join  := A.joinK Ex
  keys  := A.keysK P.lev SK
  table := A.tableK P.lev SK
  clo   := A.closeK P.cl SK
  zero  := A.zeroK Ex
  bits  := A.bitsK P.cl SK

/-- THE LOOKUP at the base: the verifier's side and its errors. -/
def lam1 (SK : PscLtK E Ex) : BkK A.St A.Out Ex := (A.bks P SK).lam1

end Dat

/-- WHAT IS ASKED OF THE LETTER SK: `Know` at the lookup's own sumchecks, and nowhere else. -/
structure Dat.Lt (A : Dat E) (P : Pl A) {Ex : ExtSpec} (SK : PscLtK E Ex) {M : Type} (Wp Kc : Type)
    (msg : M → A.J → E) : Prop where
  tie   : (A.tie P.tie).LtK SK Wp Kc msg (A.pl - 2)
  parts : (A.partsD P.wP P.cP).LtK SK Wp Kc msg (A.m - 1)
  keys  : SidesLt (B := A.kb) SK Wp Kc msg (A.part P.lev 0) (A.tailP P.lev) A.XS id
  table : LtS (A.tabT P.lev).tree SK Wp Kc msg (A.tabT P.lev).n'
  clo   : SK.CoreK M Wp Kc (A.En P.cl).par fun ms => ext0 (msg ms)
  bits  : SK.FullK M Wp Kc (A.BT P.cl).par fun ms => ext0 (msg ms)

/-- Each stretch is knowledge sound between its joints, for every letter that is at the sumchecks
laid. -/
theorem bks_knows (p : ℕ) [CharP E p] (A : Dat E) (P : Pl A) (Ex : ExtSpec) (Kc M Wp : Type)
    (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (hA : A.toPub.Adm p) (hL : A.Lt P SK Wp Kc msg) :
    (A.bks P SK).Knows R0 msg Mu where
  head := head_know p A P.tie Ex Kc M Wp SK R0 msg Mu (A.pl - 2) (Nat.sub_add_cancel hA.planes) hA
      hL.tie
  parts := partsXK_know A P.wP P.cP SK M Wp Kc R0 msg Mu hA.some hL.parts
  join := A.join_know hA.room Ex Kc M Wp R0 msg Mu
  keys := A.keys_know P.lev SK Kc M Wp R0 msg Mu hA.some (fun i hi => (hA.bits i hi).1) hL.keys
  table := A.table_know P.lev SK Kc M Wp R0 msg Mu hA.tabs hL.table
  clo := A.close_know P.cl Kc M Wp SK R0 msg Mu hL.clo
  zero := A.zero_know Ex Kc M Wp R0 msg Mu
  bits := A.bits_know P.cl Kc M Wp SK R0 msg Mu hL.bits

/-- THE LOOKUP IS KNOWLEDGE SOUND, for every letter that is at the sumchecks laid. -/
theorem lam1_know (p : ℕ) [CharP E p] (A : Dat E) (P : Pl A) (Ex : ExtSpec) (Kc M Wp : Type)
    (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (hA : A.toPub.Adm p) (hL : A.Lt P SK Wp Kc msg) :
    (A.lam1 P SK).Know (A.jtIn R0 msg Mu) (A.jtOut R0 msg) :=
  (A.bks P SK).lam1_know R0 msg Mu (bks_knows p A P Ex Kc M Wp SK R0 msg Mu hA hL)

/-- Each stretch is knowledge sound between its joints, at the library's own sumcheck. -/
theorem bks_knows_lib (p : ℕ) [CharP E p] (A : Dat E) (P : Pl A) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop)
    (hA : A.toPub.Adm p) : (A.bks P (PscLtK.lib E Ex)).Knows R0 msg Mu :=
  have four := A.four_know_lib P.cl Ex hA.room Kc M Wp R0 msg Mu
  { head := head_know_lib p A P.tie Ex Kc M Wp R0 msg Mu (A.pl - 2)
      (Nat.sub_add_cancel hA.planes) hA
    parts := partsXK_lib A P.wP P.cP M Wp Kc R0 msg Mu hA.some
    join := four.1
    keys := A.keys_know P.lev (PscLtK.lib E Ex) Kc M Wp R0 msg Mu hA.some (fun i hi => (hA.bits i
        hi).1)
      (A.keys_lt_lib P.lev Kc M Wp msg)
    table := A.table_know P.lev (PscLtK.lib E Ex) Kc M Wp R0 msg Mu hA.tabs (A.table_lt_lib P.lev Kc
        M Wp msg)
    clo := four.2.1
    zero := four.2.2.1
    bits := four.2.2.2 }

/-- THE LOOKUP IS KNOWLEDGE SOUND, at the library's own sumcheck. -/
theorem lam1_know_lib (p : ℕ) [CharP E p] (A : Dat E) (P : Pl A) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop)
    (hA : A.toPub.Adm p) :
    (A.lam1 P (PscLtK.lib E Ex)).Know (A.jtIn R0 msg Mu) (A.jtOut R0 msg) :=
  (A.bks P (PscLtK.lib E Ex)).lam1_know R0 msg Mu (bks_knows_lib p A P Ex Kc M Wp R0 msg Mu hA)

end
end Lk6

#print axioms Lk6.lam1_know
#print axioms Lk6.lam1_know_lib
