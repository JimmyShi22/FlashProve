-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldValue.lean: WHAT `Key.toldOfChain` AND `Key.toldOfMade` RETURN, WHERE
THEY RETURN, WITH THE GROUPS HANDED IN AS A LIST. General laws on the text of
Johnson/Desc/Key/Source.lean. Statements with proofs. Nothing is evaluated.

`toldOfChain` lays, for each sending, the trees with their tenants and the tenants' groups
(`rootsWithGroups` at `groupsAtLabel` of the sending's label), adds the trees that go in a round of
their own, sorts by rounds and drops the rounds. Its two guards decide whether it returns, not what.
`groupsAtLabel` cuts a label by `String.splitOn` and reads a numeral by `String.toNat?`. Here the
labels' groups are handed in as a list, so that the value names neither.

  `toldAtG`, `toldsG`: one sending's trees with its groups handed in, each with its round; along a
    chain's sendings and a list of their groups.
  `toldMore`: the trees that go in a round of their own, as the routine lays them.
  `toldVal c gss off e held`: the value: these, sorted by rounds, the rounds dropped.
  `toldsG_map`: `toldsG` at the list of the labels' groups is a map over the sendings.
  `toldOfChain_value`: where `toldOfChain` returns t, t is `toldVal` at the labels' groups and the
    plan's offset. The values of the `mapM`: `OnBytes.Maker.mapM_eq_map`
    (OnBytes/Maker/TablesPath.lean).
  `toldOfChain_eq`: so, where it returns at all, it returns `toldVal`.
  `heldMask S`: the message that the shared chain's own masks hold, as `toldOfPlans` lays it.
  `toldOfMade_eq`: where `toldOfMade m` returns at all, it returns the three chains' `toldVal`.
IT TAKES A RETURN TO GIVE A VALUE: that the routines return at any chain or any m is not shown here;
which groups the labels have is a premise.
Limits. The outer sort's key is the round, and two trees may bear one round. The routine is a
function: at one input it returns one list, so the order of such trees is fixed by the list as it
stands before the sort (the sendings' order, then the trees that go in a round of their own) and by
`List.mergeSort`'s text. Which order that is, is not said here.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.GroupsStruck
import OnBytes.Maker.TablesPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- One sending's trees, with its messages' groups handed in, each with its round; [] where no trees
can be laid, which is not reached where `toldOfChain` returns. -/
def toldAtG (codes : Codes) (off : Nat) (x : Sending) (gs : List (List Nat)) :
    List (Nat × ProofFile.Root) :=
  ((rootsWithGroups codes x.sent gs).map fun l => l.map fun r => (x.entry - 1 - off, r)).getD []

/-- The same along a chain's sendings and a list of their groups. -/
def toldsG (codes : Codes) (off : Nat) :
    List Sending → List (List (List Nat)) → List (List (Nat × ProofFile.Root))
  | x :: xs, g :: gs => toldAtG codes off x g :: toldsG codes off xs gs
  | _, _ => []

/-- The trees that go in a round of their own, each with its round. -/
def toldMore (e : List Sent) (held : Option OracleNotice) : List (Nat × ProofFile.Root) :=
  e.map fun t =>
    (t.round, { logLength := t.a, words := t.W, tenants := held.toList.map ProofFile.tenantOf })

/-- What `toldOfChain` returns, with the labels' groups handed in. -/
def toldVal (c : ChainSends) (gss : List (List (List Nat))) (off : Nat) (e : List Sent)
    (held : Option OracleNotice) : List ProofFile.Root :=
  (((toldsG c.codes off c.sends gss).flatten ++ toldMore e held).mergeSort
    fun a b => a.1 ≤ b.1).map (·.2)

/-- `toldsG` at the list of the labels' groups is a map over the sendings. -/
theorem toldsG_map (codes : Codes) (off : Nat) : ∀ xs : List Sending,
    toldsG codes off xs ((xs.map (·.label)).map groupsAtLabel) =
      xs.map fun x => toldAtG codes off x (groupsAtLabel x.label)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, toldsG]
    rw [toldsG_map codes off xs]

/-- **Where `toldOfChain` returns, what it returns.** -/
theorem toldOfChain_value {a : String} {c : ChainSends} {P : Fmt.Plan} {e : List Sent}
    {held : Option OracleNotice} {t : List ProofFile.Root} {gss : List (List (List Nat))}
    (hg : (c.sends.map (·.label)).map groupsAtLabel = gss)
    (h : toldOfChain a c P e held = .ok t) :
    t = toldVal c gss (P.entries.length - P.rounds.length) e held := by
  subst hg
  unfold toldOfChain at h
  obtain ⟨plain, _, h⟩ := ok_of_bind h
  obtain ⟨l, hl, h⟩ := ok_of_bind h
  have hl' := some_of_elim hl
  have el : l = c.sends.map fun x =>
      toldAtG c.codes (P.entries.length - P.rounds.length) x (groupsAtLabel x.label) :=
    OnBytes.Maker.mapM_eq_map _ [] c.sends l hl'
  unfold toldVal toldMore
  rw [toldsG_map, ← el]
  dsimp only at h
  split at h
  · obtain ⟨_, hy, _⟩ := ok_of_bind h
    exact nomatch hy
  · exact (Except.ok.inj h).symm

/-- **Where `toldOfChain` returns at all, it returns `toldVal`.** -/
theorem toldOfChain_eq (a : String) (c : ChainSends) (P : Fmt.Plan) (e : List Sent)
    (held : Option OracleNotice) (gss : List (List (List Nat))) (off : Nat)
    (ho : P.entries.length - P.rounds.length = off)
    (hg : (c.sends.map (·.label)).map groupsAtLabel = gss)
    (hr : ∃ t, toldOfChain a c P e held = .ok t) :
    toldOfChain a c P e held = .ok (toldVal c gss off e held) := by
  obtain ⟨t, ht⟩ := hr
  rw [ht, toldOfChain_value hg ht, ho]

/-- The message that each of the shared chain's own masks holds. -/
def heldMask (S : LinShape) : Option OracleNotice :=
  S.testOmega.head?.map fun st => foldMaskNotice (ioppFoldShape st {})

/-- **Where `toldOfMade m` returns at all, it returns the three chains' `toldVal`.** -/
theorem toldOfMade_eq (m : Made) (g₀ g₁ g₂ : List (List (List Nat))) (o₀ o₁ o₂ : Nat)
    (ho₀ : (plan₀ m).entries.length - (plan₀ m).rounds.length = o₀)
    (ho₁ : (plan₁ m).entries.length - (plan₁ m).rounds.length = o₁)
    (ho₂ : (plan₂ m).entries.length - (plan₂ m).rounds.length = o₂)
    (hg₀ : (m.key.1.sends.map (·.label)).map groupsAtLabel = g₀)
    (hg₁ : (m.key.2.1.sends.map (·.label)).map groupsAtLabel = g₁)
    (hg₂ : (m.key.2.2.sends.map (·.label)).map groupsAtLabel = g₂)
    (hr : ∃ T, toldOfMade m = .ok T) :
    toldOfMade m = .ok
      (toldVal m.key.1 g₀ o₀ [] none,
        toldVal m.key.2.1 g₁ o₁ (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds)
          (heldMask (shapeK m)),
        toldVal m.key.2.2 g₂ o₂ [] none) := by
  obtain ⟨T, hT⟩ := hr
  have h := hT
  unfold toldOfMade toldOfPlans at h
  dsimp only at h
  obtain ⟨t₀, h₀, h⟩ := ok_of_bind h
  obtain ⟨t₁, h₁, h⟩ := ok_of_bind h
  obtain ⟨t₂, h₂, h⟩ := ok_of_bind h
  rw [hT, ← Except.ok.inj h, toldOfChain_value hg₀ h₀, toldOfChain_value hg₁ h₁,
    toldOfChain_value hg₂ h₂]
  rw [show m.p.chains.key.oneTime.given.plan = plan₀ m from rfl,
    show m.p.chains.key.shared.given.plan = plan₁ m from rfl,
    show m.p.chains.key.second.given.plan = plan₂ m from rfl, ho₀, ho₁, ho₂]
  rfl

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.toldsG_map
#print axioms Johnson.AtFull.KeyBack.toldOfChain_value
#print axioms Johnson.AtFull.KeyBack.toldOfChain_eq
#print axioms Johnson.AtFull.KeyBack.toldOfMade_eq
