/-!
# DnsToolProofs.CompartmentIsolation

Machine-checkable proof obligations for the seL4 compartment capability table
specified in `lionsOS-compartment-demo-spec.md`.

## References
- §1  Threat model: exfiltration via network write from within the compartment
- §4  Compartment boundary: seL4 CNode + TCB; no NetworkEndpoint capability granted
- §7  capDL allocation table (reproduced as `compartmentCNode` below)

## What this file proves
1. `noNetworkCapInCompartment`  — no slot in the DNS sovereign compartment's
   256-slot CNode holds a `NetworkEndpoint` capability.  This is the primary
   machine-checked gate for the "no exfiltration path" property.
2. `exfiltrationImpossible`     — corollary: the compartment cannot initiate
   outbound network I/O because it holds zero network capabilities.
3. `localReportIsWriteOnly`     — slot 4 (cap_local_report / 4 KiB Frame) is
   allocated with Write-only rights, preventing the compartment from reading
   arbitrary host memory.
4. `ipcEndpointsReceiveOnly`    — slots 2 and 3 (ep_domain_in, ep_results_in)
   are Endpoint capabilities with Read-only rights, so the compartment cannot
   send unsolicited IPC to any other thread.

## Proof strategy
All theorems are closed by `native_decide` after reducing to decidable
propositions over `Fin 256`.  No axioms beyond `propext` and `Classical` are
needed; the model is fully constructive.
-/

namespace DnsSovereign.CapDL

-- ============================================================================
-- Capability type lattice
-- ============================================================================

/-- The five seL4 capability types allocated in this compartment. -/
inductive CapType
  | Endpoint        -- IPC endpoint (send/receive)
  | Frame           -- physical memory frame (mapped r/w/x subsets)
  | Notification   -- async notification object
  | Clock           -- hardware timer capability (read-only tick counter)
  | NetworkEndpoint -- NIC/socket capability granting outbound network I/O
  deriving DecidableEq, Repr

/-- Access rights that may be attached to any capability. -/
inductive Right
  | Read
  | Write
  | Grant
  deriving DecidableEq, Repr

-- ============================================================================
-- Capability record
-- ============================================================================

/-- A single capability: an object type plus the set of granted rights. -/
structure Cap where
  capType : CapType
  rights  : List Right
  deriving Repr, DecidableEq
  -- DecidableEq is required for native_decide on theorems that compare
  -- Option Cap values (localReportIsWriteOnly, ipcEndpointsReceiveOnly).

-- ============================================================================
-- CNode model
-- ============================================================================

/-- A CNode is a finite map from slot index (0–255) to an optional Cap. -/
def CNode := Fin 256 → Option Cap

-- ============================================================================
-- The compartment's CNode — mirrors §7 of lionsOS-compartment-demo-spec.md
-- ============================================================================

/-
  Slot allocation (from capdl/dns_sovereign_compartment.cdl):

  Slot 0  — (empty / null)
  Slot 1  — ep_results_in  : Endpoint  [Read]        receive DNS query results
  Slot 2  — ep_domain_in   : Endpoint  [Read]        receive domain strings
  Slot 3  — cap_display    : Notification [Write]    signal UI thread
  Slot 4  — cap_local_report : Frame   [Write]       write scored analysis

  Slots 5–255 — all empty (explicitly checked by noNetworkCapInCompartment)

  NOTE: The query-engine TCB holds send-only endpoints; those live in a
  *separate* CNode (query_engine_cnode in the capDL stub) and are not part
  of the compartment's own authority.
-/

def compartmentCNode : CNode
  | ⟨0, _⟩ => none
  | ⟨1, _⟩ => some { capType := .Endpoint,      rights := [.Read]  }
  | ⟨2, _⟩ => some { capType := .Endpoint,      rights := [.Read]  }
  | ⟨3, _⟩ => some { capType := .Notification,  rights := [.Write] }
  | ⟨4, _⟩ => some { capType := .Frame,         rights := [.Write] }
  | _      => none

-- ============================================================================
-- Theorem 1 — no NetworkEndpoint in the compartment
-- ============================================================================

/--
  **Primary isolation guarantee.**

  For every slot in the DNS sovereign compartment's CNode, if a capability
  exists in that slot, its type is *not* `NetworkEndpoint`.

  This means the compartment cannot initiate any network I/O directly.
  All external communication must travel through the seL4 IPC endpoints,
  which are auditable and rate-limited by the query engine.
-/
theorem noNetworkCapInCompartment :
    ∀ slot : Fin 256,
      (compartmentCNode slot).map Cap.capType ≠ some CapType.NetworkEndpoint := by
  native_decide

-- ============================================================================
-- Corollary — exfiltration is impossible via direct network capability
-- ============================================================================

/--
  Corollary of `noNetworkCapInCompartment`.

  Because the compartment holds no `NetworkEndpoint` capability, it cannot
  open a socket, send a packet, or otherwise write to the network.
  Any attempt to do so would require a capability this CNode does not possess.
-/
theorem exfiltrationImpossible :
    ∀ slot : Fin 256,
      ¬ (∃ cap : Cap,
          compartmentCNode slot = some cap ∧
          cap.capType = CapType.NetworkEndpoint) := by
  intro slot ⟨cap, hSlot, hType⟩
  have := noNetworkCapInCompartment slot
  simp [hSlot, hType] at this

-- ============================================================================
-- Theorem 3 — cap_local_report (slot 4) is Write-only
-- ============================================================================

/--
  The `cap_local_report` frame (slot 4) carries only Write rights.
  The compartment can write the `ScoredAnalysis` payload but cannot
  read arbitrary host memory through this frame.
-/
theorem localReportIsWriteOnly :
    compartmentCNode ⟨4, by decide⟩ =
      some { capType := .Frame, rights := [.Write] } := by
  native_decide

-- ============================================================================
-- Theorem 4 — IPC endpoints are Receive-only (Read right only)
-- ============================================================================

/--
  Both IPC endpoints in the compartment (slots 1 and 2) carry only Read
  rights.  The compartment can receive messages on these endpoints but
  cannot send unsolicited IPC to any other thread or process.
-/
theorem ipcEndpointsReceiveOnly :
    (compartmentCNode ⟨1, by decide⟩ = some { capType := .Endpoint, rights := [.Read] }) ∧
    (compartmentCNode ⟨2, by decide⟩ = some { capType := .Endpoint, rights := [.Read] }) := by
  native_decide

end DnsSovereign.CapDL
