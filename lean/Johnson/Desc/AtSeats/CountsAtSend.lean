-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/CountsAtSend.lean: THE NUMBERS' TWO COUNTS AT THE
PLACES OF THE KINDS K1 AND K13, AT THE NUMBERS CLOSED OVER THE IOP's OWN SUB-PROTOCOLS
(Numbers.atBlocks, Johnson/Desc/First/NumbersAtBlocks.lean). A joining of what lies:
told_succ_ps (Johnson/Desc/First/ToldSucc.lean: the two counts go on by what the
sub-protocol at the place tells) and told_counts (Johnson/Desc/K1/Law/ToldCounts.lean: a sending of
K1 tells as many trees as its layout has, and under them as many tenants as it sends messages). A
law file; no running text imports it.
  can_of_own: the kind's own test on its parameters holds "the trees can be laid"
  counts_at_send: along a written list of places without a place twice: where the k-th
      sub-protocol tells what K1's text tells at the place P, and P passes its own test: the count
      of trees goes on by (layOf P).shapes.size, the count of messages by P.sent.size
  counts_at_quiet: where it tells nothing: both counts stay
  told_sendAtS, told_commitAtS, told_laterAt, told_firstAtS: what K1's sub-protocols tell: K1's
      text, by unfolding
  told_andThen: a joined sub-protocol tells what its two parts tell
  told_atM3, told_rowsB, told_atM4, told_chainEnd: the kind K13's batching, its rows behind W's
      commitment and a chain's last sub-protocol tell nothing; M:4 tells what the sub-protocol that
      commits to W tells

What is not claimed. Which sub-protocol stands at which number of the first chain; that the chain's
places are the written list, without a place twice (places_scope, placesW_nodup [the latter is
declared nowhere in this library], in scope); that the composed meaning's N (P5J.At.N) is the
numbers so closed. Nothing on the verifier's state. Nothing on soundness.

-/
import Johnson.Desc.First.ToldSucc
import Johnson.Desc.K1.Law.ToldCounts
import Johnson.Desc.K1.Places
import Johnson.Desc.K1.First
import Johnson.Desc.K13.AtS
import Johnson.Desc.ChainEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model _root_.Desc.Plain
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces told_succ_ps)

/-- The kind's own test on its parameters holds "the trees can be laid". -/
theorem can_of_own {P : Par} (h : planOkOwn P = true) : Own.treesCan P.codes P.sent = true := by
  unfold planOkOwn at h
  have h1 := (Bool.and_eq_true_iff.1 h).1
  unfold planOk at h1
  simp only [Bool.and_eq_true] at h1
  exact h1.1.2

section
variable {St Cl : Type} (N : Numbers) (s : Params.ReqShape) (links : List ModelPart)
  (bs : List (Block St Cl)) (ps : List Place)

/-- **At a sending of the kind K1.** -/
theorem counts_at_send (hps : blockPlaces bs = ps) (hn : ps.Nodup) (k : Nat) (b : Block St Cl)
    (hb : bs[k]? = some b) (P : Par) (ho : b.oracles.flatten = (oracles P).flatten)
    (hB : planOkOwn P = true) :
    (N.atBlocks s links bs).treesAt ps[k + 1]? =
        (N.atBlocks s links bs).treesAt ps[k]? + (layOf P).shapes.size ∧
      (N.atBlocks s links bs).msgsAt ps[k + 1]? =
        (N.atBlocks s links bs).msgsAt ps[k]? + P.sent.size := by
  have h := told_succ_ps N s links bs ps hps hn k b hb
  have hc := told_counts P (can_of_own hB)
  rw [ho, hc.1, hc.2] at h
  exact h

/-- **Where nothing is told.** -/
theorem counts_at_quiet (hps : blockPlaces bs = ps) (hn : ps.Nodup) (k : Nat) (b : Block St Cl)
    (hb : bs[k]? = some b) (ho : b.oracles.flatten = []) :
    (N.atBlocks s links bs).treesAt ps[k + 1]? = (N.atBlocks s links bs).treesAt ps[k]? ∧
      (N.atBlocks s links bs).msgsAt ps[k + 1]? = (N.atBlocks s links bs).msgsAt ps[k]? := by
  have h := told_succ_ps N s links bs ps hps hn k b hb
  rw [ho] at h
  exact h

end

/-! ## What our sub-protocols tell -/

variable {Cl : Type}

theorem told_sendAtS (P : Par) : (sendAtS P : Block S Cl).oracles = oracles P := rfl

theorem told_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    (commitAtS P link moment arrays : Block S Cl).oracles = oracles P := rfl

theorem told_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    (laterAt q gp link piece moment arrays : Block S Cl).oracles =
      oracles (parLater q gp link piece moment) := rfl

theorem told_firstAtS (q : Params.First) (gp : GPar) :
    (firstSegmentOpening q gp : Block S Cl).oracles = oracles (firstPar q gp) := rfl

theorem told_andThen {T : Type} (name : String) (p q : Block T Cl) :
    (p.andThen name q).oracles = p.oracles ++ q.oracles := rfl

theorem flatten_replicate_nil {α : Type} : ∀ n : Nat,
    (List.replicate n ([] : List α)).flatten = []
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatten_cons, flatten_replicate_nil n]; rfl

theorem told_atM3 (p : K13.Where) : (K13.atM3 (Cl := Cl) p).oracles.flatten = [] := by
  have e : (K13.atM3 (Cl := Cl) p).oracles =
      ([] ++ List.replicate (2 + p.lin.kCol) []) ++ [] := rfl
  rw [e, List.append_nil, List.nil_append, flatten_replicate_nil]

theorem told_rowsB (p : K13.Where) : (K13.rowsB (Cl := Cl) K13.atS p).oracles.flatten = [] := rfl

theorem told_atM4 (p : K13.Where) (commitW : Block S Cl) :
    (K13.atM4 p commitW).oracles.flatten = commitW.oracles.flatten := by
  unfold K13.atM4
  rw [told_andThen, List.flatten_append, told_rowsB, List.append_nil]

theorem told_chainEnd {T : Type} (chain piece : Nat) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (asks : T → ChainEnd.Clauses) :
    (ChainEnd.chainEnd (Cl := Cl) chain piece sealed inFront asks).oracles.flatten = [] := by
  cases sealed <;> rfl

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.counts_at_send
#print axioms VerifiableInference.Desc.K1.counts_at_quiet
#print axioms VerifiableInference.Desc.K1.told_atM3
#print axioms VerifiableInference.Desc.K1.told_rowsB
#print axioms VerifiableInference.Desc.K1.told_atM4
#print axioms VerifiableInference.Desc.K1.told_chainEnd
