// n in B/B ?  Same automaton as bbq.c, with a generation-stamped hash set (no O(n) clearing per n).
// Prints each non-member n (n % 3 != 0) with the size of its reachable carry set.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int inB(long r){ if(r<=0) return 0; while(r){ long c=((r%3)+3)%3; if(c==0) return 0; c = c==2?-1:1; r=(r-c)/3; } return 1; }
static long *key; static uint32_t *gen; static long cap=1<<20, mask; static uint32_t G=0;
static long *q; static long qcap;
static void grow(void);
static int insert(long r){ // 1 if new
  uint64_t h=((uint64_t)r*0x9E3779B97F4A7C15ULL)>>20; long i=h&mask;
  while(gen[i]==G){ if(key[i]==r) return 0; i=(i+1)&mask; }
  gen[i]=G; key[i]=r; return 1; }
static long count;
static int member(long n, long *reach){
  G++; long h=0,t=0; count=0; insert(0); q[t++]=0; count=1;
  while(h<t){ long r=q[h++];
    for(int d=-1; d<=1; d+=2){ long v=r+n*d; long c=((v%3)+3)%3; if(c==0) continue; c=c==2?-1:1; long r2=(v-c)/3;
      if(d==1 && (r2==0||inB(r2))){ *reach=count; return 1; }
      if(insert(r2)){ count++; if(t>=qcap){ qcap*=2; q=realloc(q,sizeof(long)*qcap);} q[t++]=r2;
        if(count*2>cap){ *reach=-1; return -1; } } } }
  *reach=count; return 0; }
int main(int argc,char**argv){
  long lo=atol(argv[1]), hi=atol(argv[2]); if(argc>3) cap=1L<<atoi(argv[3]); mask=cap-1;
  key=malloc(sizeof(long)*cap); gen=calloc(cap,sizeof(uint32_t)); qcap=1<<16; q=malloc(sizeof(long)*qcap);
  long cnt=0, over=0;
  for(long n=lo;n<=hi;n++){ if(n%3==0) continue; long R; int m=member(n,&R);
    if(m==0){ cnt++; printf("%ld %ld\n",n,R); fflush(stdout); }
    else if(m<0){ over++; printf("%ld OVERFLOW\n",n); fflush(stdout); } }
  fprintf(stderr,"[%ld,%ld]: %ld non-members, %ld overflow\n",lo,hi,cnt,over); return 0; }
