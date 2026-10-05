// Exact search storing only the smaller half of the ordered magnitude list.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Entry {uint64_t key,code;};
int D,M,T2,T4; vector<int>sq,ft; vector<Entry>table;
uint64_t candidates=0,visited=0; bool solved=false;
uint64_t pack(int a,int b){return(uint64_t(a)<<32)|uint32_t(b);}
bool signcheck(array<int,16>z,array<int,16>&answer){
 int s=0,c=0;for(int x:z){s+=x;c+=x*x*x;}if((c-s)%48)return false;
 array<pair<uint64_t,unsigned>,256>left;
 for(unsigned mask=0;mask<256;mask++){int a=0,b=0;for(int j=0;j<8;j++)if(mask>>j&1){int x=z[j];a+=x;b+=x*x*x;}left[mask]={pack(a,b),mask};}
 sort(left.begin(),left.end());
 for(unsigned mask=0;mask<256;mask++){int a=0,b=0;for(int j=0;j<8;j++)if(mask>>j&1){int x=z[j+8];a+=x;b+=x*x*x;}if(a>s/2||b>c/2)continue;
 auto found=lower_bound(left.begin(),left.end(),make_pair(pack(s/2-a,c/2-b),0u));
 if(found!=left.end()&&found->first==pack(s/2-a,c/2-b)){for(int j=0;j<8;j++){answer[j]=(found->second>>j&1)?z[j]:-z[j];answer[j+8]=(mask>>j&1)?z[j+8]:-z[j+8];}return true;}}
 return false;
}
void smallhalf(int depth,int start,int s2,int s4,uint64_t code){
 if(depth==8){if(s2<=T2/2&&s4<=T4/2)table.push_back({pack(s2,s4),code});return;}
 int left=8-depth;
 for(int i=start;i<M;i++){
  if(s2+(left+8)*sq[i]>T2||int64_t(s4)+int64_t(left+8)*ft[i]>T4)break;
  if(s2+left*sq[i]>T2/2||int64_t(s4)+int64_t(left)*ft[i]>T4/2)break;
  smallhalf(depth+1,i,s2+sq[i],s4+ft[i],code|(uint64_t(i)<<(7*depth)));
 }
}
void largehalf(int depth,int start,int s2,int s4,uint64_t code){
 if(solved)return;
 if(depth==8){
  visited++;int first=code&127;
  if(s2<T2/2||s4<T4/2||T2-s2>8*sq[first]||int64_t(T4-s4)>8LL*ft[first])return;
  uint64_t wanted=pack(T2-s2,T4-s4);
  auto begin=lower_bound(table.begin(),table.end(),wanted,[](Entry x,uint64_t k){return x.key<k;});
  for(auto it=begin;it!=table.end()&&it->key==wanted;it++){
   if(int((it->code>>49)&127)>first)continue;
   candidates++;array<int,16>z{},answer{};
   for(int j=0;j<8;j++){z[j]=2*((it->code>>(7*j))&127)+1;z[j+8]=2*((code>>(7*j))&127)+1;}
   if(signcheck(z,answer)){
    long long sums[5]={};for(int x:answer){long long p=1;for(int j=0;j<5;j++){sums[j]+=p;p*=x;}}
    if(sums[0]!=16||sums[1]||sums[2]!=T2||sums[3]||sums[4]!=T4)exit(2);
    cout<<"FOUND D="<<D<<" candidates="<<candidates<<"\n";
    ofstream out("degree4_sixteen_mitm.json");out<<"{\"degree\":4,\"size\":16,\"centered_denominator\":"<<D<<",\"centered_numerators\":[";
    for(int j=0;j<16;j++){cout<<answer[j]<<" ";if(j)out<<",";out<<answer[j];}out<<"]}\n";cout<<"\n";solved=true;return;
   }
  }return;
 }
 int left=8-depth;
 if(s2+left*sq.back()<T2/2||int64_t(s4)+int64_t(left)*ft.back()<T4/2)return;
 for(int i=start;i<M;i++){
  if(s2+left*sq[i]>T2-8||int64_t(s4)+int64_t(left)*ft[i]>T4-8)break;
  largehalf(depth+1,i,s2+sq[i],s4+ft[i],code|(uint64_t(i)<<(7*depth)));
 }
}
int main(int argc,char**argv){
 D=argc>1?atoi(argv[1]):75;if(D<15||D>135||D%30!=15)return 1;
 M=(D+1)/2;T2=16*D*D/3;T4=16LL*D*D*D*D/5;sq.resize(M);ft.resize(M);
 for(int i=0;i<M;i++){int x=2*i+1;sq[i]=x*x;ft[i]=x*x*x*x;}
 smallhalf(0,0,0,0,0);cerr<<"D="<<D<<" stored small halves="<<table.size()<<"\n";
 sort(table.begin(),table.end(),[](Entry a,Entry b){return a.key<b.key;});
 largehalf(0,0,0,0,0);
 if(!solved)cout<<"NO RULE D="<<D<<"; large halves="<<visited<<"; exact candidates="<<candidates<<"\n";
}
