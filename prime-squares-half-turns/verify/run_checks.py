"""Run positive and mutation controls serially in a single foreground process."""
from verify import check

print(f'Positive control: {check()} exact audit assertions passed', flush=True)
mutants = ['half_turn', 'quarter_as_involution', 'drop_oddness',
           'drop_primality', 'unconditional_coprime', 'orientation_sign']
for mutant in mutants:
    try:
        check(mutant)
    except AssertionError as error:
        print(f'Rejected {mutant}: {error}', flush=True)
    else:
        raise AssertionError(f'UNDETECTED MUTATION: {mutant}')
print(f'All {len(mutants)} deliberate mutations rejected', flush=True)
