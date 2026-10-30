-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Law.lean: the law of the constraint (fold) in the linear claim's shared rounds,
as statements: definitions of propositions alone.

The shared rounds test no equation: they lay linear constraints on committed messages. What a
constraint says of words is OnBytes.Means.Says: the sums end where the statement's tables end.
Main names:
  LaysOfW, LaysW   where "SPLIT" says yes it has laid just one constraint more on each of the two
                   groups, and what these two say together of any words is what (fold) says.
  Placed           the two messages of (fold) have main tables of the sizes of their layouts.
  FoldMeansW       what (fold) says of words is the equation FoldEq in K.
  FoldSoundOf, FoldSound   for words that are fixed before z_fd: if omega_col is not
                   col_psi_lo(u) on M's rows, then at no more than kRow |K| ^ (kRow - 1) points z_fd
                   can "SPLIT" say yes and all constraints on the two groups hold of the words.

What is not claimed. Nothing is proved in this file. Nothing on how z_fd is drawn, on how words are
tied to what a prover has sent, on (rec_gamma) or (loc_x), on an honest prover or on hiding.
FoldSound speaks of ONE assignment of words for both groups: that the two proximity tests speak of
one word for o_sp, o_u and o_omega, fixed before z_fd, is the tests' law's to show. It leans on no
premise on decoding or on a code's distance. omega_col is tied on the rows of M alone.

-/
import Johnson.Desc.K14.Law.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-- LAYS, of any function in the place of "SPLIT". -/
def LaysOfW (sp : Par → St → List Fmt.RoundView → Option St) : Prop :=
  ∀ (p : Par) (d d' : St) (r : Fmt.RoundView), p.S.sharedSplitNeeded = true → sp p d [r] = some d' →
    ∃ row a b : Row, fold p.S d.loc (linLayOmega d.st.codes p.S) = some row ∧
      rowsOn d' d.loc.gOmega = rowsOn d d.loc.gOmega ++ [a] ∧
      rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ [b] ∧
      ∀ (T : Statement) (m : Words K),
        Means.Says ρ T a m → Means.Says ρ T b m → Means.Says ρ T row m

/-- **LAYS.** -/
def LaysW : Prop := LaysOfW ρ split

/-- The two messages of (fold) are two, and have main tables of the sizes of their layouts, which
hold the vectors. -/
structure Placed (T : Statement) (S : LinShape) (l : Lin) (lay : VectorLay) : Prop where
  two : l.oOmega ≠ l.oU.oracle
  hasOmega : T.has l.oOmega .main = true
  hasU : T.has l.oU.oracle .main = true
  bitsOmega : T.tableBits l.oOmega .main = lay.bits
  bitsU : T.tableBits l.oU.oracle .main = l.oU.lay.bits
  roomOmega : S.kRow ≤ lay.bits
  roomU : S.kLo + S.kRow ≤ l.oU.lay.bits

/-- **MEANS**, for (fold). -/
def FoldMeansW : Prop :=
  ∀ (T : Statement) (S : LinShape) (l : Lin) (lay : VectorLay) (row : Row),
    fold S l lay = some row → Placed T S l lay → ∀ m : Words K,
      (Means.Says ρ T row m ↔ FoldEq S ((l.psiSh.take S.kLo).map ρ.val) (l.zFd.map ρ.val)
        (omegaOf l lay m) (uOf l m))

open Classical in
/-- The law of (fold), of any function in the place of "SPLIT". d: the state in front of the round
in which z_fd is drawn. -/
def FoldSoundOf [Fintype K] (sp : Par → St → List Fmt.RoundView → Option St) : Prop :=
  ∀ (p : Par) (d : St) (T : Statement) (m : Words K), p.S.sharedSplitNeeded = true →
    Placed T p.S d.loc (linLayOmega d.st.codes p.S) →
    (∃ j < p.S.matrixRows, omegaOf d.loc (linLayOmega d.st.codes p.S) m j ≠
      ∑ t ∈ Finset.range (2 ^ p.S.kLo),
        eqK ((d.loc.psiSh.take p.S.kLo).map ρ.val) t * uOf d.loc m (t + 2 ^ p.S.kLo * j)) →
    (Finset.univ.filter fun z : Fin p.S.kRow → K =>
      ∃ (zs : List E) (r : Fmt.RoundView) (d' : St), zs.map ρ.val = List.ofFn z ∧
        sp p { d with loc := { d.loc with zFd := zs } } [r] = some d' ∧
        Means.AllSay ρ T (rowsOn d' d.loc.gOmega) m ∧
        Means.AllSay ρ T (rowsOn d' d.loc.gU) m).card ≤
      p.S.kRow * Fintype.card K ^ (p.S.kRow - 1)

/-- **The law of (fold).** -/
def FoldSound [Fintype K] : Prop := FoldSoundOf ρ split

end Desc.K14.Law
