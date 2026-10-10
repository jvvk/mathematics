from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
for mutation in [None,'root_sign','coefficient','cap_dimension','derivative','mixture','ball_density']:
    cmd=['timeout','120','nice','-n','15',sys.executable,str(root/'verify.py')]
    if mutation:cmd+=['--mutant',mutation]
    result=subprocess.run(cmd,capture_output=True,text=True)
    if mutation:
        assert result.returncode==1 and 'AssertionError' in result.stderr,(mutation,result.stdout,result.stderr)
        print('REJECTED:',mutation,flush=True)
    else:
        assert result.returncode==0,(result.stdout,result.stderr)
        print(result.stdout.strip(),flush=True)
