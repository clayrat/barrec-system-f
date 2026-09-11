(** * Hindley-Milner inference — planned

    Adapt W-in-Coq-master.zip in this namespace, preserving its term,
    monotype, scheme, substitution, freshness, and generalization
    interfaces. Split unification into specification, failure certificates,
    and the algorithm before exposing runW here.

    Check equality before the occurs check and prove failure soundness.
    The existing lexicographic termination measure can be retained.

    This scaffold contains no inference algorithm or assumed theorem. *)
