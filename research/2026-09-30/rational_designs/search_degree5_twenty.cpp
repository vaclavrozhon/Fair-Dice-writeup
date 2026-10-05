// Exact search for a symmetric degree-five rule with20 rational nodes.
// Ten nonnegative y magnitudes, x=(1+-y)/2; eight even numerators
// and two odd numerators over an odd denominator D, as forced by2-adics.
#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <vector>
using namespace std;
struct Key{int64_t a,b;bool operator==(const Key&o)const{return a==o.a&&b==o.b;}};
struct Hash{size_t operator()(const Key&x)const{return uint64_t(x.a)*0x9e3779b97f4a7c15ULL^uint64_t(x.b);}};
struct Entry{Key k;array<int,4> v;};
int main(){
 for(int D: {15,45,75,105,135,165}){
  int64_t target2=10LL*D*D/3,target4=2LL*D*D*D*D;
  vector<Entry> entries;
  unordered_map<Key,array<int,4>,Hash> table;
  for(int a=0;a<=D;a+=2)for(int b=a;b<=D;b+=2)
   for(int c=b;c<=D;c+=2)for(int d=c;d<=D;d+=2){
    int64_t q=0,r=0;for(int x:{a,b,c,d}){q+=x*x;r+=int64_t(x)*x*x*x;}
    if(q>target2||r>target4)continue;
    Key k{q,r};array<int,4> v{a,b,c,d};
    if(table.emplace(k,v).second)entries.push_back({k,v});
   }
  cerr<<"D="<<D<<" distinct_even_four_sums="<<entries.size()<<endl;
  for(int a=1;a<=D;a+=2)for(int b=a;b<=D;b+=2){
   int64_t q=target2-a*a-b*b,r=target4-int64_t(a)*a*a*a-int64_t(b)*b*b*b;
   for(auto&e:entries){
    if(e.k.a>q||e.k.b>r)continue;
    auto it=table.find({q-e.k.a,r-e.k.b});if(it==table.end())continue;
    cout<<"{\"D\":"<<D<<",\"magnitudes\":["<<a<<","<<b;
    for(int x:e.v)cout<<","<<x;for(int x:it->second)cout<<","<<x;
    cout<<"]}"<<endl;return 0;
   }
  }
 }
 cout<<"{\"found\":false}"<<endl;
}
