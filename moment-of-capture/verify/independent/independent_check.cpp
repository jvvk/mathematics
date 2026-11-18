#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;

// A sufficient state: the last value, and the nonzero indicators of
// the last k values (oldest bit at position k-1).
struct State {
    uint64_t bits;
    unsigned value;
    bool operator==(const State& q) const {
        return bits == q.bits && value == q.value;
    }
};
State advance(State q, int k) {
    unsigned v = (q.value + ((q.bits >> (k-1)) & 1)) % 3;
    return {((q.bits << 1) | (v != 0)) & ((uint64_t(1) << k)-1), v};
}

int main() {
    cout << "k,period,mu,s,z,z-mu\n";
    uint64_t total = 0;
    unsigned captures = 0, no_capture = 0;
    for (int k=2; k<=60; ++k) {
        State initial{1,1}, slow=advance(initial,k), fast=advance(advance(initial,k),k);
        uint64_t steps=1;
        while (!(slow == fast) && steps < 200000000ULL) {
            slow=advance(slow,k); fast=advance(advance(fast,k),k); ++steps;
        }
        if (!(slow == fast)) {
            cerr << "UNRESOLVED k=" << k << " after " << steps << " Floyd iterations\n";
            return 2;
        }
        uint64_t entry=0;
        slow=initial;
        while (!(slow == fast)) {
            slow=advance(slow,k); fast=advance(fast,k); ++entry;
        }
        uint64_t period=1;
        fast=advance(slow,k);
        while (!(slow == fast)) { fast=advance(fast,k); ++period; }

        // Independently reconstruct using the literal squared recurrence.
        uint64_t end=k+entry+2*period+4*k+20;
        vector<unsigned char> x(end+1,0);
        x[k]=1;
        State q=initial;
        for (uint64_t n=k+1; n<=end; ++n) {
            x[n]=(x[n-1]+x[n-k]*x[n-k])%3;
            q=advance(q,k);
            assert(q.value == x[n]);
            uint64_t b=0;
            for (uint64_t j=n-k+1; j<=n; ++j) b=(b<<1)|(x[j]!=0);
            assert(b == q.bits);
        }
        uint64_t mu=0;
        for (uint64_t n=1; n+period<=end; ++n)
            if (x[n]!=x[n+period]) mu=n;
        assert(mu<=k+entry);

        const int G=(k+2)/4;
        uint64_t z=0, s=0, previous_zero=0;
        int gaps=0;
        for (uint64_t n=k+1; n<=end; ++n) {
            // Lemma 17 on every consecutive zero pair in the full sample.
            if (x[n]!=0) continue;
            if (previous_zero && n-previous_zero==4) {
                assert(x[n-3]==1 && x[n-1]==2);
                assert(x[n-2]==1 || x[n-2]==2);
                ++gaps;
            } else gaps=0;
            previous_zero=n;
            if (!z && gaps>=G) { z=n; s=n-4*G; }
        }
        if (k%4!=2 && k%4!=3) {
            assert(period!=4);
            // Proposition 13 does not assert capture for these classes.
            z=0; s=0;
        } else assert((period==4) == (z!=0));
        if (z) {
            ++captures;
            assert(k%4==2 || k%4==3);
            unsigned cyc[4]={0,1,unsigned(k%4==2 ? 1 : 2),2};
            for (uint64_t n=z; n<=end; ++n) assert(x[n]==cyc[(n-z)%4]);
            if (k>=6) {
                int t=k/4;
                assert(G==t+1);
                assert(s>=uint64_t(k+5));
                assert(z-k==s+unsigned(k%4==2 ? 2 : 1));
                // Independently enumerate the images; check their endpoints.
                vector<uint64_t> a,b,c;
                for (uint64_t m=s; m<=z-4; m+=4) {
                    a.push_back(m+4-k); b.push_back(m+1-k); c.push_back(m+2-k);
                    assert(x[m+4-k]!=0 && x[m+1-k]!=0);
                    assert((x[m+2-k]!=0)+(x[m+3-k]!=0)==1);
                }
                assert(a.front()==s-k+4 && a.back()==s+unsigned(k%4==2 ? 2 : 1));
                assert(b.front()==s-k+1 && b.back()==s-unsigned(k%4==2 ? 1 : 2));
                assert(c.front()==s-k+2 && c.back()==s-unsigned(k%4==2 ? 0 : 1));
                for (uint64_t n=z-1; n<=end; ++n) assert(x[n]==x[n-4]);
                assert(x[z-2]!=x[z-6]);
                assert(mu==z-6);
                assert(x[s-4]!=0);
                if (k%4==2) assert(x[z-6]==2 && x[z-2]==1);
                else assert(x[s-5]==0 && x[s-1]!=0 && x[z-6]==1 && x[z-2]==2);
            }
        } else ++no_capture;
        cout << k << ',' << period << ',' << mu << ',';
        if (z) cout << s << ',' << z << ',' << int64_t(z)-int64_t(mu);
        else cout << "-,-,-";
        cout << '\n';
        total+=end;
    }
    cout << "PASS: 59 values of k; " << captures << " captures; " << no_capture
         << " noncaptures; " << total << " reconstructed terms (including initial prefixes).\n";
}
