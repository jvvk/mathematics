import LeanProofs

-- Lemma 2.2 (length exchange) and Lemma 2.3 (turn exchange)
#check Spans.length_cmp
#print axioms Spans.length_cmp
#check Spans.turn_cmp
#print axioms Spans.turn_cmp
-- Theorem 1, parts 1 to 4 and the first/last turns
#check Spans.lengths_unimodal
#print axioms Spans.lengths_unimodal
#check Spans.shortest_at_end
#print axioms Spans.shortest_at_end
#check Spans.half_lt_arg
#check Spans.endpoint_arg
#print axioms Spans.endpoint_arg
#check Spans.last_second_shortest
#print axioms Spans.last_second_shortest
#check Spans.turns_valley
#print axioms Spans.turns_valley
#check Spans.longest_at_smallest_turn
#print axioms Spans.longest_at_smallest_turn
#check Spans.first_turn_descends
#check Spans.last_turn_ascends
#print axioms Spans.last_turn_ascends
-- Proposition 5.1: a_4 = 3
#check Spans.a4_eq_three
#print axioms Spans.a4_eq_three
