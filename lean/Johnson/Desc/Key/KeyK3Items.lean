-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyK3Items.lean: the table of joints of the key file: K3's three items at its general face (Johnson/Desc/First/Look/K3LookupGeneral.lean: Face · HeardG · PlaneClaim · planesG), over the base letters of KeyK3W.lean; and the layer's tie,
as a statement. Definitions alone. No Mathlib.
The border: between K3's block and the layer of rows. There the ledger G holds all the lookup's slots taken, but the leaves' sumcheck is still open (by a run: KeyShape.lean's head): so each item is said at the ledger in which that sumcheck is closed:
G' := what the kind's own planesG leaves of G (`closedAt`): a function of what was heard and of G alone.
  FormsObjects   K3's files: «the forms that the hearing left are worth 0»: every member of HeardG.rows is worth 0 in the world of G' and the witness
  WorthPlanes    «the leaves' sumcheck's row, the bits' value and the counts' sum are 0 at the true values of the planes»: for each of planesG's three claims: lead + scalar · ⟨v, the bits⟩ = 0, v the product vector of the claim's pairs,
                 the bits the witness's (bit i: KeyK3W.bitVec)
  WorthKeys      «for each part, the form that stands in HeardG.keys beside its key tree's last point is worth the part's key vector's extension at that point»: one sentence a part: the form is on alpha − key (K3LookupGeneral.lean:198-200): so:
                 it is worth Σ_k eq(point, k) · (alpha − key k), the point read the lowest variable first (HeardG has the highest first; K3Key.keyClaims turns it likewise), the keys the witness's (KeyK3W.keyVec), padding counted
  K3At S         three readers more of the state: the ledger · what was heard · the table of homes
  LayerFacts     what the layer does, as facts on the readers: behind it lookup l's rows are K3Key.groupRows of (G', the homes, what was heard), by the program's planesAt; its pending rows are Wf.pendingRow of K3Key.keyClaims, a part each
  LayerTie       **the exchange, stated**: rows l and kclaims l behind ⟹ the three items in front. Not proved here. What it wants: (i) rowOfAff's row holds ⟺ the form is worth 0 (maskSide's identity: tried by a run at made-up mask entries) ·
                 (ii) rowOfPlane's row holds ⟺ the claim at the true bits (bitVec reads the bit as the library does: read_bitVecL, Johnson/RunOne/Law/TiePlanes.lean, is the ground here) · (iii) pendingRow ∘ keysOf's row on the matrix holds ⟺ the part's sentence (Wf.pendingRow's head's
                 computation; padding's share; the offset): by reading alone · and the field's laws on machine elements: the words' test.
Limits: KeyWords.lean's. The shift: a key file's lookups have one function: theta is 0 there and enters nowhere: not said for a face with a shift. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyK3W
import Johnson.Desc.Key.KeyLaws
import Johnson.Desc.First.Look.K3Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.K3 (Face HeardG PlaneClaim planesG faceOfLkp groupRows keyClaims)

/-- The kind's three claims on the planes, and the ledger in which the leaves' sumcheck is closed. -/
def closedAt (f : Face) (g : HeardG) (G : Fork) : Option (List PlaneClaim × Fork) := (planesG f g G []).map fun x => (x.1, x.2.1)

/-- ⟨v, the bits⟩: v the product vector with these pairs, over the mu + d variables. -/
def planeSum (f : Face) (pairs : List (E × E)) (bit : Nat → E) : E :=
  sumE (2 ^ (f.mu + f.d)) fun i => mulE (({ scalar := oneE, pairs := pairs } : Tensor).entry i) (bit i)

/-- **forms l "objects".** -/
def FormsObjects (same : E → E → Prop) (f : Face) (g : HeardG) (G : Fork) (home : Array Slot) (mk : Slot → E) : Prop :=
  ∃ cl G', closedAt f g G = some (cl, G') ∧ ∀ a ∈ g.rows.toList, Zero same G' home mk a

/-- **worth l "planes".** -/
def WorthPlanes (same : E → E → Prop) (f : Face) (g : HeardG) (G : Fork) (home : Array Slot) (mk : Slot → E) (bit : Nat → E) : Prop :=
  ∃ cl G', closedAt f g G = some (cl, G') ∧ cl.length = 3 ∧
    ∀ c ∈ cl, c.lead.ents.isEmpty = true ∧ (∀ t ∈ c.lead.slots, t.1 < home.size) ∧ same (addE (affAt G' home mk c.lead) (mulE c.scalar (planeSum f c.pairs bit))) zeroE

/-- **worth l "keys"**: one sentence a part. key i k: key number k of part i. -/
def WorthKeys (same : E → E → Prop) (f : Face) (g : HeardG) (G : Fork) (home : Array Slot) (mk : Slot → E) (key : Nat → Nat → E) : Prop :=
  g.keys.length = f.parts.length ∧ ∃ cl G', closedAt f g G = some (cl, G') ∧
    ∀ x ∈ g.keys.zipIdx, x.1.2.ents.isEmpty = true ∧ (∀ t ∈ x.1.2.slots, t.1 < home.size) ∧
      same (affAt G' home mk x.1.2) (sumE (2 ^ f.parts.getD x.2 0) fun k => mulE ((Tensor.eq x.1.1.toList.reverse).entry k) (subE g.alpha (key x.2 k)))

/-- **Three readers more of the state.** -/
structure K3At (S : Type) where
  fork : S → Option Fork
  heard : S → Option HeardG
  home : S → Array Slot

section
variable {P S Cells M : Type} (K : KPlan) (R : KRead Cells M) (X : KReaders S) (Y : K3At S)
  /- the item «ranges» and the codes: the plan's -/
  (x : OnBytes.Params.WfPublic) (codes : Codes)

/-- Lookup l's public record, as the block LKP takes it. -/
def lkpOf (l : Nat) : Option Lkp.Public := (Wf.lookupsOf x K.m)[l]?

/-- **The two letters of KMeaning that were K3's, filled.** -/
def formsAt (l : Nat) (run : String) (a : P × S) (_ : Strs) (w : Wit Cells Unit M) : Prop :=
  run = "objects" ∧ ∃ Sg g G, lkpOf K x l = some Sg ∧ Y.heard a.2 = some g ∧ Y.fork a.2 = some G ∧ FormsObjects R.same (faceOfLkp Sg) g G (Y.home a.2) (mkOf K R w)

def worthAt (l : Nat) (what : String) (a : P × S) (_ : Strs) (w : Wit Cells Unit M) : Prop :=
  ∃ Sg L g G, lkpOf K x l = some Sg ∧ K.lookups[l]? = some L ∧ Y.heard a.2 = some g ∧ Y.fork a.2 = some G ∧
    ((what = "planes" ∧ WorthPlanes R.same (faceOfLkp Sg) g G (Y.home a.2) (mkOf K R w) (bitVec x codes l fun i => R.val (R.of w 1) .main i)) ∨
     (what = "keys" ∧ WorthKeys R.same (faceOfLkp Sg) g G (Y.home a.2) (mkOf K R w) (keyVec K.m L (matOf K R w))))

/-- **What the layer does, as facts on the readers.** s: in front; s': behind. -/
structure LayerFacts (l : Nat) (s s' : S) : Prop where
  tables : SameTables (X.st s') (X.st s)
  rows : ∀ Sg g G cl G', lkpOf K x l = some Sg → Y.heard s = some g → Y.fork s = some G → closedAt (faceOfLkp Sg) g G = some (cl, G') →
    X.rowsAt s' l = groupRows (Wf.planesAt x codes l) G' (Y.home s) g.rows.toList cl
  keys : ∀ Sg L g G cl G', lkpOf K x l = some Sg → K.lookups[l]? = some L → Y.heard s = some g → Y.fork s = some G → closedAt (faceOfLkp Sg) g G = some (cl, G') →
    X.keysAt s' l = (keyClaims Sg G' (Y.home s) g).map fun ks => (L.parts.zip ks).map fun q => Wf.pendingRow K.m L q.1 q.2 (Wf.eqPlaces K.m q.2.point)
  /-- in front: something was heard, a ledger is open, and the kind's own closing returns -/
  there : ∃ Sg g G c, lkpOf K x l = some Sg ∧ Y.heard s = some g ∧ Y.fork s = some G ∧ closedAt (faceOfLkp Sg) g G = some c

variable (near : Nat → P × S → Strs → Prop) (other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)

/-- The first chain's meaning with K3's letters filled. -/
def meaningK : KMeaning P S (Wit Cells Unit M) := meaning₁ K R X near (formsAt K R Y x) (worthAt K R Y x codes) other

/-- **THE LAYER's TIE: THE EXCHANGE: STATED, NOT PROVED.** -/
def LayerTie (l : Nat) : Prop :=
  ∀ (p : P) (s s' : S) (y : Strs) (w : Wit Cells Unit M), LayerFacts K X Y x codes l s s' →
    (meaningK K R X Y x codes near other).rows l (p, s') y w → (meaningK K R X Y x codes near other).kclaims l (p, s') y w →
      (meaningK K R X Y x codes near other).forms l "objects" (p, s) y w ∧ (meaningK K R X Y x codes near other).worth l "planes" (p, s) y w ∧
        (meaningK K R X Y x codes near other).worth l "keys" (p, s) y w

end

/-- A TOOTH, WITH CODE, FOR (i): maskSide's identity at given mask entries: the form's worth is (the public value) − (the mask form's value). How many of these forms have a mask side, and at how many the identity holds. -/
def maskFits (G : Fork) (home : Array Slot) (mk : Slot → E) (as : List Aff) : Nat × Nat × Nat :=
  as.foldl (fun (c : Nat × Nat × Nat) a =>
    match K3.maskSide G home a with
    | some y => (c.1 + 1, c.2.1 + 1, if affAt G home mk a == subE y.2 (formAt mk y.1) then c.2.2 + 1 else c.2.2)
    | none => (c.1 + 1, c.2.1, c.2.2)) (0, 0, 0)

/-- THE TOOTH's CONTROL: the form's worth at the entries mk against the mask form's value at OTHER entries mk': at how many forms the identity still holds: due: just those whose mask form is empty or blind to the change. -/
def maskFitsAt (G : Fork) (home : Array Slot) (mk mk' : Slot → E) (as : List Aff) : Nat :=
  (as.filter fun a => match K3.maskSide G home a with
    | some y => affAt G home mk a == subE y.2 (formAt mk' y.1)
    | none => false).length

end VerifiableInference.Desc.Key
