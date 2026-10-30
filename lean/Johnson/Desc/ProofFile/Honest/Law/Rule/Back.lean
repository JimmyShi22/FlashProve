-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Back.lean: from what has been produced back to the library's
disclosed view. `back` is a function that is written out (it is `noncomputable`: `viewAt` decides
membership classically). Its arguments are the three values that the rounds without a challenge
send, what has been produced (`Laid`, Honest/Law/Rule/Session.lean),
the instance, the verifier's message (the typed challenges) and the external answers (beside the
parameters `C`, `D`, `tF`, `tJ`, `t3`, `F` and `silent`). It builds the typed transcript that shows
exactly that, and returns its disclosed view (`Iop.DView`, Iop/InteractiveOracleProof.lean). Its type names
no private input, no coin and no table, except for the external answers: these hold the external
string's symbols at the positions that the protocol reads, and `back` puts them into the view whole.
The type does not exclude one: `TF`, `TJ`, `T3` and `Xi` are type parameters, and a `Laid` is
whatever the caller supplies.

  0  `viewAt`, `dview_viewAt`   at any protocol all of whose oracles are blinded
  1  `orcOff`, `msgOff`, `trOff`   a round's typed message and a chain's transcript, from what is
     shown
  2  `trWhole`, `back`   the whole transcript; the disclosed view
  3  `back_eq`   when a transcript's disclosed view is `back`: three hypotheses on it

Limits.
  * Definitions, and two lemmas on them.
  * That the strategies' transcript meets the three hypotheses of `back_eq` is not proved in this
    file; it is proved, under its own hypotheses, in `backAt_of` (Honest/Law/BackAt.lean), which
    applies `back_eq`.
  * The nonce of a round with proof of work is 0, as in Honest/Strat.lean: the hypothesis of
    `back_eq` on the plain parts can be met only by a transcript whose plain parts have that 0.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Record
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (RDT WholeD uLT roundT PosT SymT chainsOf)
open _root_.Run.PQ (CK SgX)

variable {Xi TF TJ T3 : Type}

/-! ## 0 A disclosed view, from a transcript and given answers -/

section
variable {X : Type} {E : Iop.ExtSpec}

open Classical in
/-- The plain parts of a transcript; external answers as they are given; the transcript's symbols at
the protocol's own reads at ρ; `none` at a position that is not read. -/
noncomputable def viewAt (Q : Iop.InteractiveOracleProof X E) (x : X) (ρ : Iop.Rho Q.shape)
    (a : E.Pos → Option E.Sym) (τ' : Iop.Tr Q.shape) : Iop.DView Q :=
  ⟨τ'.plains, a, fun p => if p ∈ Q.reads x ρ τ'.plains then some (τ'.read p) else none⟩

/-- At a protocol all of whose oracles are blinded: the disclosed view of a transcript is `viewAt`
at any transcript with the same plain parts and the same symbols at the reads. -/
theorem dview_viewAt (Q : Iop.InteractiveOracleProof X E) (hbl : ∀ p, Q.blinded p = true) (x : X) (y : E.Str)
    (τ τ' : Iop.Tr Q.shape) (ρ : Iop.Rho Q.shape) (hρ : τ.rho = ρ) (hpl : τ.plains = τ'.plains)
    (hrd : ∀ p ∈ Q.reads x ρ τ'.plains, τ.read p = τ'.read p) :
    Q.dview x y τ = viewAt Q x ρ (Q.extAns x ρ y) τ' := by
  subst hρ
  unfold Iop.InteractiveOracleProof.dview viewAt
  rw [hpl]
  congr 1
  funext p
  by_cases hp : p ∈ Q.reads x τ.rho τ'.plains
  · rw [if_pos (Or.inl hp), if_pos hp, hrd p hp]
  · rw [if_neg (fun h => h.elim hp fun e => absurd ((hbl p).symm.trans e) (by decide)), if_neg hp]

end

/-! ## 1 A round; a chain -/

/-- A round's oracle part, from the columns that are shown: at a position of the n-th tree, the
first column that is listed there, its words by their numbers; 0 where no column is listed or a word
is missing. As `orcOf` (Honest/Strat.lean), with a list of columns where that has a table. Lists of
columns beyond the declared trees, and words beyond the width, are dropped. -/
def orcOff : (ts : List Fmt.Shape) → List (List (Nat × List UInt64)) → (p : PosT ts) → SymT ts p
  | _ :: _, l, .inl x => fun i => ((((l.head?.getD []).lookup x.val).getD [])[i.val]?).getD 0
  | _ :: ts, l, .inr p => orcOff ts l.tail p

/-- A round's typed message, from what is shown of it. As `msgOf` (Honest/Strat.lean). The written 0
is the nonce of a round with proof of work, as there. -/
def msgOff (C : CK) (d : RDT) (y : Shown) : (roundT C d).up.Msg :=
  (orcOff d.trees y.cols, Iop.GPlain.mk d.entry.work (plainOf d.items y.vals) (0 : ℕ))

/-- A chain's transcript, from what is shown round by round and the typed challenges. Where the list
of shown rounds is shorter than the declared rounds, the empty `Shown` (no item, no column) takes a
missing round's place; entries beyond the declared rounds are dropped. -/
def trOff (C : CK) : (ds : List RDT) → List Shown → Iop.Rho (uLT C ds) → Iop.Tr (uLT C ds)
  | [], _, _ => ()
  | d :: ds, ys, ρ => (msgOff C d (ys.head?.getD ⟨[], []⟩), ρ.1, trOff C ds ys.tail ρ.2)

/-! ## 2 The whole transcript -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)

/-- The whole transcript, from the three values that the rounds without a challenge send, what has
been produced, and the typed challenges. -/
def trWhole (v : TF × TJ × T3) (L : Laid) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    Iop.Tr (chainsOf C D tF tJ t3).sh :=
  (((), v.1), ρ.1, Iop.Tr.app (trOff C D.ds₁ (L.first.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₁ ρ))
    ((((), v.2.1), ((chainsOf C D tF tJ t3).rhoJ ρ).1,
      Iop.Tr.app (trOff C D.ds₂ (L.shared.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₂ ρ))
        ((((), v.2.2), (Iop.Rho.snd (s := (chainsOf C D tF tJ t3).s₂)
            ((chainsOf C D tF tJ t3).rhoJ ρ).2).1,
          trOff C D.ds₃ (L.second.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₃ ρ)) :
          Iop.Tr (chainsOf C D tF tJ t3).sh₃)) : Iop.Tr (chainsOf C D tF tJ t3).shJ))

variable (F : FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)

/-- **The library's disclosed view, from what has been produced**: the plain parts; the external
answers as they are given; the symbols at the protocol's own reads. -/
noncomputable def back (v : TF × TJ × T3) (L : Laid) (x : Xi)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (a : (Iop.oneExternalString (2 ^ D.a) SgX).Pos → Option (Iop.oneExternalString (2 ^ D.a) SgX).Sym) : Iop.DView (batchOf C
                                  D tF tJ t3 F silent).loc :=
  viewAt (batchOf C D tF tJ t3 F silent).loc x ρ a (trWhole C D tF tJ t3 v L ρ)

/-! ## 3 When a transcript's disclosed view is `back` -/

/-- The disclosed view of a transcript with these challenges, these plain parts, and these symbols
at the protocol's own reads is `back`. -/
theorem back_eq (v : TF × TJ × T3) (L : Laid) (x : Xi) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (y : (Iop.oneExternalString (2 ^ D.a) SgX).Str) (τ : Iop.Tr (chainsOf C D tF tJ t3).sh) (hρ : τ.rho = ρ)
    (hpl : τ.plains = (trWhole C D tF tJ t3 v L ρ).plains)
    (hrd : ∀ p ∈ (batchOf C D tF tJ t3 F silent).loc.reads x ρ (trWhole C D tF tJ t3 v L ρ).plains,
      τ.read p = (trWhole C D tF tJ t3 v L ρ).read p) :
    (batchOf C D tF tJ t3 F silent).loc.dview x y τ = back C D tF tJ t3 F silent v L x ρ ((batchOf C
        D tF tJ t3 F silent).loc.extAns x ρ y) :=
  dview_viewAt (batchOf C D tF tJ t3 F silent).loc (fun _ => rfl) x y τ (trWhole C D tF tJ t3 v L ρ)
      ρ hρ hpl hrd

end

end ProofFile.Honest

#print axioms ProofFile.Honest.dview_viewAt
#print axioms ProofFile.Honest.back_eq
