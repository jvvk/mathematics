#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <string>
#include <vector>
using Shape = std::vector<int>;
using U = uint64_t;
struct State { int shape, row; std::vector<int> next; };
struct Level { std::vector<Shape> shapes; std::map<Shape,int> index; std::vector<State> states; std::map<std::pair<int,int>,int> state_index; };
int N, W, M;
std::vector<Level> levels;
std::vector<U> support, intervals, diagonal;
std::ofstream count_dump;
std::vector<U> alternating_prefix;
int majorization_failure=-1;
void checked_add(U &value, U term) {
    assert(term<=std::numeric_limits<U>::max()-value);
    value+=term;
}
void partitions(int rem,int max,Shape &s,std::vector<Shape>&out) {
    if (!rem) { out.push_back(s); return; }
    for(int p=std::min(rem,max);p>=1;--p) { s.push_back(p);partitions(rem-p,p,s,out);s.pop_back(); }
}
std::vector<int> prefix(const Shape &s) {
    std::vector<int> p(N); int total=0;
    for(int i=0;i<N;++i) { if(i<(int)s.size()) total+=s[i];p[i]=total; }
    return p;
}
bool leq(const std::vector<int>&a,const std::vector<int>&b) {
    for(int i=0;i<N;++i) if(a[i]>b[i]) return false;
    return true;
}
Shape composition(int mask) {
    Shape a;int prev=0;
    for(int i=1;i<N;++i) if(mask>>(i-1)&1) { a.push_back(i-prev);prev=i; }
    a.push_back(N-prev);return a;
}
std::pair<Shape,Shape> bounds(int mask) {
    Shape a=composition(mask),lo=a,col(N,0),hi;
    std::sort(lo.rbegin(),lo.rend());int x=0;
    for(int p:a) { for(int j=0;j<p;++j) ++col[x+j]; x+=p-1; }
    for(int k=1;k<=*std::max_element(col.begin(),col.end());++k)
        hi.push_back(std::count_if(col.begin(),col.end(),[k](int z){return z>=k;}));
    return {lo,hi};
}
void descend(int n,int mask,const std::vector<U>&dist) {
    if(n==N) {
        std::vector<U> c(levels[N].shapes.size(),0);
        for(size_t j=0;j<dist.size();++j) checked_add(c[levels[N].states[j].shape],dist[j]);
        for(size_t j=0;j<c.size();++j) if(c[j]) {
            if(count_dump.is_open()) {
                count_dump<<mask<<" ";
                for(int part:levels[N].shapes[j]) count_dump<<part<<",";
                count_dump<<" "<<c[j]<<"\n";
            }
            support[(size_t)mask*W+j/64]|=U(1)<<(j%64);
            assert(c[j]<=std::numeric_limits<U>::max()/c[j]);
            checked_add(diagonal[mask],c[j]*c[j]);
        }
        if(!alternating_prefix.empty()) {
            std::sort(c.rbegin(),c.rend());U total=0;
            for(size_t j=0;j<c.size();++j) {
                checked_add(total,c[j]);
                if(total>alternating_prefix[j] && majorization_failure<0) majorization_failure=mask;
            }
        }
        return;
    }
    for(int bit=0;bit<2;++bit) {
        std::vector<U> nd(levels[n+1].states.size(),0);bool any=false;
        for(size_t j=0;j<dist.size();++j) if(dist[j]) {
            auto &state=levels[n].states[j];
            for(int k:state.next) if((levels[n+1].states[k].row>state.row)==bool(bit)) {
                checked_add(nd[k],dist[j]);any=true;
            }
        }
        if(any) descend(n+1,mask|(bit<<(n-1)),nd);
    }
}
void print_shape(const Shape &s) { std::cout<<"[";for(size_t i=0;i<s.size();++i) std::cout<<(i?",":"")<<s[i];std::cout<<"]"; }
int main(int argc,char**argv) {
    N=argc>1?std::stoi(argv[1]):14; assert(N>=1 && N<=22);
    auto start=std::chrono::steady_clock::now(); levels.resize(N+1);
    for(int n=1;n<=N;++n) {
        Shape empty;partitions(n,n,empty,levels[n].shapes);
        for(size_t j=0;j<levels[n].shapes.size();++j) {
            auto &s=levels[n].shapes[j];levels[n].index[s]=j;
            for(size_t r=0;r<s.size();++r) if(r+1==s.size()||s[r]>s[r+1]) {
                int k=levels[n].states.size();levels[n].states.push_back({(int)j,(int)r,{}});
                levels[n].state_index[{j,r}]=k;
            }
        }
    }
    for(int n=1;n<N;++n) for(auto &state:levels[n].states) {
        auto s=levels[n].shapes[state.shape];
        for(size_t r=0;r<=s.size();++r) if(r==0||r==s.size()||s[r-1]>s[r]) {
            Shape ns=s; if(r==s.size())ns.push_back(1);else++ns[r];
            int j=levels[n+1].index.at(ns);
            state.next.push_back(levels[n+1].state_index.at({j,r}));
        }
    }
    W=(levels[N].shapes.size()+63)/64;M=1<<(N-1);
    support.assign((size_t)M*W,0);intervals=support;diagonal.assign(M,0);
    if(argc>3) count_dump.open(argv[3]);
    if(argc>2 && std::string(argv[2])=="majorization") {
        std::vector<U> dist{1};
        for(int n=1;n<N;++n) {
            std::vector<U> nd(levels[n+1].states.size(),0);
            for(size_t j=0;j<dist.size();++j) if(dist[j])
                for(int k:levels[n].states[j].next)
                    if((levels[n+1].states[k].row>levels[n].states[j].row)==bool(n%2)) checked_add(nd[k],dist[j]);
            dist.swap(nd);
        }
        alternating_prefix.assign(levels[N].shapes.size(),0);
        for(size_t j=0;j<dist.size();++j) checked_add(alternating_prefix[levels[N].states[j].shape],dist[j]);
        std::sort(alternating_prefix.rbegin(),alternating_prefix.rend());
        U running=0;
        for(U &value:alternating_prefix) { checked_add(running,value);value=running; }
    }
    descend(1,0,{1});std::cerr<<"tableau counts completed for n="<<N<<"\n";
    int gaps=0; std::vector<std::vector<int>> prefixes;
    for(auto &s:levels[N].shapes)prefixes.push_back(prefix(s));
    for(int mask=0;mask<M;++mask) {
        auto [lo,hi]=bounds(mask);auto lp=prefix(lo),hp=prefix(hi);
        for(size_t j=0;j<prefixes.size();++j) if(leq(lp,prefixes[j])&&leq(prefixes[j],hp))
            intervals[(size_t)mask*W+j/64]|=U(1)<<(j%64);
        bool gap=false;
        for(int k=0;k<W;++k) { assert(!(support[(size_t)mask*W+k]&~intervals[(size_t)mask*W+k]));gap|=support[(size_t)mask*W+k]!=intervals[(size_t)mask*W+k]; }
        gaps+=gap;
    }
    U best=*std::max_element(diagonal.begin(),diagonal.end()),second=0;
    int alt=0;for(int i=0;i<N-1;i+=2)alt|=1<<i;
    std::cout<<"{\"n\":"<<N<<",\"maximum\":"<<best<<",\"alternating_value\":"<<diagonal[alt]<<",\"maximisers\":[";
    bool comma=false;for(int mask=0;mask<M;++mask)if(diagonal[mask]==best){std::cout<<(comma?",":"")<<mask;comma=true;}else second=std::max(second,diagonal[mask]);
    std::cout<<"],\"second\":"<<second<<",\"noninterval_supports\":"<<gaps<<std::flush;
    if(argc>2 && std::string(argv[2])=="majorization") { std::cout<<",\"weak_majorization_failure\":"<<majorization_failure<<"}\n";return 0; }
    if(argc>2 && std::string(argv[2])=="maxima") { std::cout<<"}\n";return 0; }
    U actual_total=0,predicted_total=0;
    for(int a=0;a<M;++a) for(int b=a;b<M;++b) {
        bool actual=false,predicted=false;
        for(int k=0;k<W;++k) if(support[(size_t)a*W+k]&support[(size_t)b*W+k]){actual=true;break;}
        if(actual) predicted=true;
        else for(int k=0;k<W;++k)if(intervals[(size_t)a*W+k]&intervals[(size_t)b*W+k]){predicted=true;break;}
        if(predicted&&!actual) {
            std::cout<<",\"counterexample_masks\":["<<a<<","<<b<<"],\"compositions\":[";
            print_shape(composition(a));std::cout<<",";print_shape(composition(b));
            std::cout<<"],\"common_interval_shapes\":[";comma=false;
            for(size_t j=0;j<levels[N].shapes.size();++j) if((intervals[(size_t)a*W+j/64]&intervals[(size_t)b*W+j/64])>>(j%64)&1){std::cout<<(comma?",":"");print_shape(levels[N].shapes[j]);comma=true;}
            std::cout<<"]}\n";return 2;
        }
        actual_total+=(a==b?1:2)*actual;predicted_total+=(a==b?1:2)*predicted;
    }
    auto seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout<<",\"f\":"<<actual_total<<",\"criterion_count\":"<<predicted_total<<",\"ordered_pairs_checked\":"<<(U(M)*M)<<",\"seconds\":"<<seconds<<"}\n";
}
