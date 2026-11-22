/* Random hitomezashi pattern on an N x N box with p-biased labels; trace every closed loop
   (each lattice point has one vertical and one horizontal stitch), record diameter and length.
   Output: histogram lines "diam count sum_length sum_length^2" for loops not touching the boundary.
   usage: loops N p reps seed */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
static uint64_t s[2];
static uint64_t rnd(void){uint64_t a=s[0],b=s[1];s[0]=b;a^=a<<23;s[1]=a^b^(a>>17)^(b>>26);return s[1]+b;}
static double unif(void){return (rnd()>>11)*(1.0/9007199254740992.0);}
int main(int argc,char**argv){
  int N=atoi(argv[1]); double p=atof(argv[2]); int reps=atoi(argv[3]); s[0]=strtoull(argv[4],0,10)*2654435761ULL+1; s[1]=0x9E3779B97F4A7C15ULL;
  int W=N+1; unsigned char*eps=malloc(W),*eta=malloc(W),*seen=malloc((size_t)W*W);
  int MAXD=N+1; double *cnt=calloc(MAXD,8),*sl=calloc(MAXD,8),*sl2=calloc(MAXD,8);
  for(int r=0;r<reps;r++){
    for(int i=0;i<W;i++){eps[i]=unif()<p?0:1; eta[i]=unif()<p?0:1;}
    memset(seen,0,(size_t)W*W);
    for(int x0=0;x0<W;x0++)for(int y0=0;y0<W;y0++){
      if(seen[(size_t)x0*W+y0])continue;
      /* trace from (x0,y0): first take its vertical stitch */
      int x=x0,y=y0,closed=1; long len=0; int minx=x,maxx=x,miny=y,maxy=y; int vert=1;
      while(1){
        seen[(size_t)x*W+y]=1;
        if(vert){ /* vertical stitch at (x,y): up if y%2==eps[x], else down */
          int ny = ((y&1)==eps[x])? y+1 : y-1;
          if(ny<0||ny>N){closed=0;break;} y=ny;
        } else {
          int nx = ((x&1)==eta[y])? x+1 : x-1;
          if(nx<0||nx>N){closed=0;break;} x=nx;
        }
        len++; vert=!vert;
        if(x<minx)minx=x; if(x>maxx)maxx=x; if(y<miny)miny=y; if(y>maxy)maxy=y;
        if(x==x0&&y==y0&&vert)break;
        if(len>4L*W*W){closed=0;break;}
      }
      if(!closed){ /* mark the rest of the open strand from the other direction */
        x=x0;y=y0;vert=0;
        while(1){ seen[(size_t)x*W+y]=1;
          if(vert){int ny=((y&1)==eps[x])?y+1:y-1; if(ny<0||ny>N)break; y=ny;}
          else {int nx=((x&1)==eta[y])?x+1:x-1; if(nx<0||nx>N)break; x=nx;}
          vert=!vert; if(seen[(size_t)x*W+y])break; }
        continue; }
      if(minx==0||miny==0||maxx==N||maxy==N)continue;
      int d=(maxx-minx)>(maxy-miny)?(maxx-minx):(maxy-miny);
      cnt[d]+=1; sl[d]+=len; sl2[d]+=(double)len*len;
    }
  }
  for(int d=0;d<MAXD;d++) if(cnt[d]>0) printf("%d %.0f %.0f %.6g\n",d,cnt[d],sl[d],sl2[d]);
  return 0;
}
