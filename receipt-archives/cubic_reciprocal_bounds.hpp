// Directed enclosures for the reciprocal Mobius moment on the same quotient grid.
// Index, Wide and rough_sieve are supplied by cubic_window_moments.cpp.
using SignedWide = __int128;
using Small = std::int64_t;
constexpr Small unit = Small(1) << 57;
constexpr Wide fine_unit = Wide(1) << 93;
constexpr Small fine_ratio = Small(1) << 36;
struct Bounds { Small lo=0, hi=0; };

Small checked_small(SignedWide n) {
    if(n < std::numeric_limits<Small>::min() || n > std::numeric_limits<Small>::max())
        throw std::overflow_error("reciprocal enclosure overflow");
    return Small(n);
}
Small down(SignedWide n, Index d) {
    return checked_small(n>=0 ? n/d : -SignedWide((Wide(-n)+d-1)/d));
}
Small up(SignedWide n, Index d) { return -down(-n,d); }
struct Accumulator {
    SignedWide lo=0, hi=0;
    void subtract(Bounds b) {lo-=b.hi; hi-=b.lo;}
    Bounds bounds() const {return {checked_small(lo),checked_small(hi)};}
};
Bounds difference(Bounds a, Bounds b) {return {a.lo-b.hi,a.hi-b.lo};}
Bounds product(Bounds weight, Bounds v) {
    if(weight.lo<0) throw std::logic_error("negative harmonic lower bound");
    return {down(SignedWide(v.lo)*(v.lo<0?weight.hi:weight.lo),unit),
            up(SignedWide(v.hi)*(v.hi<0?weight.lo:weight.hi),unit)};
}
Bounds exact_ratio(Index num, Index den) {
    return {down(SignedWide(num)*unit,den),up(SignedWide(num)*unit,den)};
}
Bounds log_near(Index num, Index den) {
    // 1 <= num/den <= 2. The atanh argument is at most 1/3.
    if(num<den || num>2*den) throw std::logic_error("log reduction");
    const Bounds z=exact_ratio(num-den,num+den), z2=product(z,z);
    Bounds term=z;
    Accumulator sum;
    for(unsigned j=0;j<24;++j) {
        sum.lo+=down(2*SignedWide(term.lo),2*j+1);
        sum.hi+=up(2*SignedWide(term.hi),2*j+1);
        term=product(z2,term);
    }
    // The rest is at most 3*(1/3)^49, smaller than one unit at scale 2^57.
    ++sum.hi;
    return sum.bounds();
}
Bounds log_ratio(Index num, Index den) {
    static const Bounds log2=log_near(2,1);
    Index k=0;
    while(num>=2*den) {den*=2;++k;}
    const Bounds r=log_near(num,den);
    return {checked_small(SignedWide(k)*log2.lo+r.lo),checked_small(SignedWide(k)*log2.hi+r.hi)};
}

void reciprocals(Index top, Index cutoff, const std::vector<Index>& queries,
                 const std::vector<std::int8_t>& mu, bool rough) {
    std::vector<Bounds> low(cutoff+1),harm(cutoff+1);
    std::vector<Small> low_count(cutoff+1), high_count(top/(cutoff+1)+1);
    SignedWide h_start=0, m_start=0;
    Index h_width=0, m_width=0;
    for(Index n=1;n<=cutoff;++n) {
        const SignedWide q=fine_unit/n;
        const Index bit=fine_unit%n!=0;
        h_start+=q;h_width+=bit;
        if(mu[n]>0) {m_start+=q;m_width+=bit;}
        if(mu[n]<0) {m_start-=q+bit;m_width+=bit;}
        low_count[n]=low_count[n-1]+mu[n];
        low[n]={down(m_start,fine_ratio),up(m_start+m_width,fine_ratio)};
        harm[n]={down(h_start,fine_ratio),up(h_start+h_width,fine_ratio)};
    }
    std::vector<Bounds> high(top/(cutoff+1)+1), harmonic_high(high.size());
    for(Index i=1;i<high.size();++i) {
        const Index n=top/i;
        const Bounds lg=log_ratio(2*n+1,2*cutoff+1), base=harm[cutoff];
        // Convexity and the midpoint remainder on every unit cell imply
        // 0 <= log((n+1/2)/(B+1/2)) - (H_n-H_B) <= 1/B^2.
        const Small correction=up(unit,cutoff*cutoff);
        harmonic_high[i]={base.lo+lg.lo-correction,base.hi+lg.hi};
    }
    auto harmonic=[&](Index n){return n<=cutoff?harm[n]:harmonic_high[top/n];};
    auto multiplier_harmonic=[&](Index n){
        Bounds v=harmonic(n);
        if(!rough) return v;
        Bounds a=harmonic(n/2),b=harmonic(n/3),c=harmonic(n/6);
        return Bounds{v.lo-up(a.hi,2)-up(b.hi,3)+down(c.lo,6),
                      v.hi-down(a.lo,2)-down(b.lo,3)+up(c.hi,6)};
    };
    std::vector<Index> smooth;
    for(Index a=1;a<=top;a*=2)
        for(Index b=a;b<=top;b*=3) smooth.push_back(b);
    std::sort(smooth.begin(),smooth.end());
    std::vector<Bounds> sources(smooth.size()+1);
    SignedWide p=0; Index width=0;
    for(size_t i=0;i<smooth.size();++i) {
        p+=fine_unit/smooth[i];width+=(fine_unit%smooth[i])!=0;
        sources[i+1]={down(p,fine_ratio),up(p+width,fine_ratio)};
    }
    auto get=[&](Index n){return n<=cutoff?low[n]:high[top/n];};
    auto count=[&](Index n){return n<=cutoff?low_count[n]:high_count[top/n];};
    auto permitted=[&](Index n){return rough ? n-n/2-n/3+n/6 : n;};
    for(Index i=top/(cutoff+1);i>0;--i) {
        const Index n=top/i;
        Bounds source=rough ? Bounds{unit,unit} :
            sources[std::upper_bound(smooth.begin(),smooth.end(),n)-smooth.begin()];
        Accumulator total{source.lo,source.hi};
        SignedWide plain=rough?1:std::upper_bound(smooth.begin(),smooth.end(),n)-smooth.begin();
        Index d=2;
        for(;d<=n/d;++d) {
            if(rough && (d%2==0 || d%3==0)) continue;
            plain-=count(n/d);
            const Bounds v=get(n/d);
            total.subtract({down(v.lo,d),up(v.hi,d)});
        }
        auto previous=multiplier_harmonic(d-1);
        Index previous_count=permitted(d-1);
        for(Index q=n/d;q>0;--q) {
            const auto next=multiplier_harmonic(n/q);
            const Index next_count=permitted(n/q);
            plain-=SignedWide(next_count-previous_count)*low_count[q];
            previous_count=next_count;
            auto block=difference(next,previous);
            block.lo=std::max<Small>(0,block.lo);
            if(block.hi<block.lo) throw std::logic_error("harmonic block");
            total.subtract(product(block,low[q]));
            previous=next;
        }
        high[i]=total.bounds();
        if(plain>SignedWide(n) || plain< -SignedWide(n)) throw std::logic_error("count outside head");
        high_count[i]=checked_small(plain);
    }
    for(Index q:queries) {
        auto b=get(top/q);
        std::cout<<"reciprocal "<<q<<' '<<b.lo<<' '<<b.hi<<' '<<count(top/q)<<'\n';
    }
}

void direct_checkpoints(Index top, std::vector<Index> nodes) {
    if(top>=(Index(1)<<30)) throw std::invalid_argument("direct sieve must be below 2^30");
    std::sort(nodes.begin(),nodes.end());
    nodes.erase(std::unique(nodes.begin(),nodes.end()),nodes.end());
    const auto mu=rough_sieve(top);
    SignedWide low=0;Index width=0;Small count=0;size_t at=0;
    for(Index d=1;d<=top;++d) {
        if(mu[d]) {
            const SignedWide q=fine_unit/d;
            const Index bit=fine_unit%d!=0;
            low+=(mu[d]>0 ? q : -q-SignedWide(bit));
            width+=bit;count+=mu[d];
        }
        if(at<nodes.size() && nodes[at]==d) {
            std::cout<<"direct "<<d<<' '<<down(low,fine_ratio)<<' '<<up(low+width,fine_ratio)<<' '<<count<<'\n';
            ++at;
        }
    }
    if(at!=nodes.size()) throw std::logic_error("missing direct node");
}
