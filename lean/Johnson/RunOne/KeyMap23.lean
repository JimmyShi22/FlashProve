-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMap23.lean. IN WHICH FORM A KIND's LAW OF A BLOCK WITH ROUNDS ENTERS THE KEY FILE's SHARED AND LAST CHAIN's TABLES. The tables' claim at a border is ONE «there is a witness» over ALL open items (L₂ | L₃). A law «a witness behind gives a
witness in front» (what Know.toLeads returns: it drops the extractor) does not give Keeps there: the riders hold at the witness behind, not at the one that the law returns. THE FORM THAT DOES: A NAMED MAP E ON WITNESSES (Johnson/Desc/Plain/OneWitness.lean):
  Map₂ | Map₃ E k a b     the promise behind ∧ for every w: the relation behind at w → the relation in front AT E a b w
  keeps₂_of_map | keeps₃_of_map   PROVED: Leads … (Map E k) gives Keeps (on k) (on (k+1)) (L k) (L (k+1)): what RowsOwed.keeps₂ | keeps₃ (Johnson/Top/Fire/Code/KeyOfRows.lean) ask of a piece
  map₂_glue | map₃_glue           PROVED: WHAT A KIND's FILES OWE: (law) with its errors: the promise behind, and AT E a b w the items that its row CLOSES (open in front, not behind) · (ride) FOR CERTAIN: every item that is open on both sides rides back from the record behind at w to the
                                  record in front at E a b w
WHICH E. The tables' witness is one for the whole file (the stored table's cells; every message by its number). A ROW THAT CLOSES THE LAST ITEM ON A PART OF IT LEAVES THAT PART FREE BEHIND: there E MUST LAY IT: the rows say which (Johnson/Desc/Key/KeyBorders23.lean: laysCells at «LIN point», which
closes pinT and the pile: nothing behind it reads the cells · lays := [3] | [5] at the two tests of the shared chain; the own test closes all three pins): at these rows «the same witness» CANNOT be had. At a row that lays nothing E := the same witness is meant. THAT NO RIDER READS WHAT E LAYS is the (ride) premise's
content there: NOT SHOWN HERE FOR ANY ROW: the table's own test laysClear (KeyBorders23.lean; evaluated: true, with controls) says it of the TYPED lists readsMsg | readsCells; that an item's holds reads no more of the witness than these lists say is proved nowhere.
Limits. Rules at the key file's tables: as empty as their premises. No block's law is shown. Nothing on soundness.

-/
import Johnson.RunOne.KeyRows23At
import Johnson.Desc.Plain.OneWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState)
open _root_.Iop (Reduction Err)

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **The law's form at the shared chain's block k.** E: the map on witnesses. -/
def Map₂ (E : (P₂ × St₂) × Fr₂.E.Str → (P₂ × St₂) × Fr₂.E.Str → Wit Cells Unit M → Wit Cells Unit M) (k : Nat) (x x' : (P₂ × St₂) × Fr₂.E.Str) : Prop :=
  on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ (k + 1) x' ∧ ∀ w, R₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1) x' w → R₂ F Fr₂ G₂ at_ S K₁ R enc rad k x (E x x' w)

/-- **At the last chain's.** -/
def Map₃ (E : (P₃ × St₃) × Fr₃.E.Str → (P₃ × St₃) × Fr₃.E.Str → Wit Cells Unit M → Wit Cells Unit M) (k : Nat) (x x' : (P₃ × St₃) × Fr₃.E.Str) : Prop :=
  on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ (k + 1) x' ∧ ∀ w, R₃ F Fr₃ G₃ at_ S K₁ R (k + 1) x' w → R₃ F Fr₃ G₃ at_ S K₁ R k x (E x x' w)

variable {F Fr₂ Fr₃ G₂ G₃ at_ S K₁ R enc rad a idx coll last₁ src off₂ off₃ t₁}

theorem keeps₂_of_map (K : Reduction ((P₂ × St₂) × Fr₂.E.Str) ((P₂ × St₂) × Fr₂.E.Str)) (ε : Err K.shape)
    (E : (P₂ × St₂) × Fr₂.E.Str → (P₂ × St₂) × Fr₂.E.Str → Wit Cells Unit M → Wit Cells Unit M) (k : Nat)
    (h : K.Leads (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k) (Map₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ E k) ε) :
    K.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ (k + 1))
      (L₂ F Fr₂ G₂ at_ S K₁ R enc rad k) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1)) ε :=
  Reduction.Leads.keepsOfMap E (R₂ F Fr₂ G₂ at_ S K₁ R enc rad k) (R₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1)) h

theorem keeps₃_of_map (K : Reduction ((P₃ × St₃) × Fr₃.E.Str) ((P₃ × St₃) × Fr₃.E.Str)) (ε : Err K.shape)
    (E : (P₃ × St₃) × Fr₃.E.Str → (P₃ × St₃) × Fr₃.E.Str → Wit Cells Unit M → Wit Cells Unit M) (k : Nat)
    (h : K.Leads (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k) (Map₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ E k) ε) :
    K.Keeps (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k) (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ (k + 1))
      (L₃ F Fr₃ G₃ at_ S K₁ R k) (L₃ F Fr₃ G₃ at_ S K₁ R (k + 1)) ε :=
  Reduction.Leads.keepsOfMap E (R₃ F Fr₃ G₃ at_ S K₁ R k) (R₃ F Fr₃ G₃ at_ S K₁ R (k + 1)) h

/-- **What a kind's files owe at the shared chain's block k.** -/
theorem map₂_glue (K : Reduction ((P₂ × St₂) × Fr₂.E.Str) ((P₂ × St₂) × Fr₂.E.Str)) (ε : Err K.shape)
    (E : (P₂ × St₂) × Fr₂.E.Str → (P₂ × St₂) × Fr₂.E.Str → Wit Cells Unit M → Wit Cells Unit M) (k : Nat)
    (law : K.Leads (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k)
      (fun x x' => on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ (k + 1) x' ∧ ∀ w, R₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1) x' w →
        ∀ i ∈ open₂ k, i ∉ open₂ (k + 1) → i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x.1 (strsOf Fr₂ x.2) (E x x' w)) ε)
    (ride : ∀ x τ x', on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k x → K.out x τ = some x' → ∀ w i, i ∈ open₂ k → i ∈ open₂ (k + 1) →
      i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x'.1 (strsOf Fr₂ x'.2) w → i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x.1 (strsOf Fr₂ x.2) (E x x' w)) :
    K.Leads (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k) (Map₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ E k) ε :=
  Reduction.Leads.glueBy E (open₂ k) (open₂ (k + 1))
    (fun i (x : (P₂ × St₂) × Fr₂.E.Str) w => i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x.1 (strsOf Fr₂ x.2) w)
    (fun i (x : (P₂ × St₂) × Fr₂.E.Str) w => i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x.1 (strsOf Fr₂ x.2) w) law ride

/-- **At the last chain's.** -/
theorem map₃_glue (K : Reduction ((P₃ × St₃) × Fr₃.E.Str) ((P₃ × St₃) × Fr₃.E.Str)) (ε : Err K.shape)
    (E : (P₃ × St₃) × Fr₃.E.Str → (P₃ × St₃) × Fr₃.E.Str → Wit Cells Unit M → Wit Cells Unit M) (k : Nat)
    (law : K.Leads (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k)
      (fun x x' => on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ (k + 1) x' ∧ ∀ w, R₃ F Fr₃ G₃ at_ S K₁ R (k + 1) x' w →
        ∀ i ∈ open₃ k, i ∉ open₃ (k + 1) → i.holds F G₃ at_ (meaning₃ S K₁ R) x.1 (strsOf Fr₃ x.2) (E x x' w)) ε)
    (ride : ∀ x τ x', on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k x → K.out x τ = some x' → ∀ w i, i ∈ open₃ k → i ∈ open₃ (k + 1) →
      i.holds F G₃ at_ (meaning₃ S K₁ R) x'.1 (strsOf Fr₃ x'.2) w → i.holds F G₃ at_ (meaning₃ S K₁ R) x.1 (strsOf Fr₃ x.2) (E x x' w)) :
    K.Leads (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k) (Map₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ E k) ε :=
  Reduction.Leads.glueBy E (open₃ k) (open₃ (k + 1))
    (fun i (x : (P₃ × St₃) × Fr₃.E.Str) w => i.holds F G₃ at_ (meaning₃ S K₁ R) x.1 (strsOf Fr₃ x.2) w)
    (fun i (x : (P₃ × St₃) × Fr₃.E.Str) w => i.holds F G₃ at_ (meaning₃ S K₁ R) x.1 (strsOf Fr₃ x.2) w) law ride

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.keeps₂_of_map
#print axioms Johnson.RunOne.KeyRows23.keeps₃_of_map
#print axioms Johnson.RunOne.KeyRows23.map₂_glue
#print axioms Johnson.RunOne.KeyRows23.map₃_glue
