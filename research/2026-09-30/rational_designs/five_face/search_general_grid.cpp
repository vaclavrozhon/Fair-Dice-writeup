// Exhaustive monotone five-row local tensors with a fixed denominator.
// Repeated coordinates and repeated columns are allowed.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <vector>
using V=std::array<int,5>;
long long dot(const V&a,const V&b){long long s=0;for(int i=0;i<5;i++)s+=a[i]*b[i];return s;}
long long triple(const V&a,const V&b,const V&c){long long s=0;for(int i=0;i<5;i++)s+=1LL*a[i]*b[i]*c[i];return s;}
long long quad(const V&a,const V&b,const V&c,const V&d){long long s=0;for(int i=0;i<5;i++)s+=1LL*a[i]*b[i]*c[i]*d[i];return s;}
bool fourth_compatible_mod(const V&a,const V&b,const V&c,int D){
 const long long P=1000003;long long m[8][6]{};
 for(int i=0;i<5;i++){m[0][i]=1;m[1][i]=a[i];m[2][i]=b[i];m[3][i]=c[i];m[4][i]=1LL*a[i]*b[i];m[5][i]=1LL*a[i]*c[i];m[6][i]=1LL*b[i]*c[i];m[7][i]=1LL*a[i]*b[i]*c[i];}
 for(int j=1;j<=3;j++)m[j][5]=5*D/3;m[7][5]=1LL*D*D*D;
 for(auto &row:m)for(auto &x:row)x=(x%P+P)%P;
 auto inv=[P](long long x){long long e=P-2,y=1;while(e){if(e&1)y=y*x%P;x=x*x%P;e>>=1;}return y;};
 int rank=0;
 for(int col=0;col<6;col++){
  int pivot=rank;while(pivot<8&&!m[pivot][col])pivot++;if(pivot==8)continue;
  for(int k=0;k<6;k++)std::swap(m[pivot][k],m[rank][k]);
  long long mul=inv(m[rank][col]);for(int k=col;k<6;k++)m[rank][k]=m[rank][k]*mul%P;
  for(int j=rank+1;j<8;j++){mul=m[j][col];for(int k=col;k<6;k++)m[j][k]=(m[j][k]-mul*m[rank][k]%P+P)%P;}
  rank++;
 }
 // A six-column augmented rank of six is a sound rational exclusion.
 return rank<=5;
}
int main(int argc,char**argv){
 int D=argc>1?std::atoi(argv[1]):12;
 bool solve_fourth=argc>2;
 if(D%3){std::cerr<<"Denominator must be divisible by three\n";return 2;}
 std::vector<V> v;
 for(int a=-D;a<=D;a++)for(int b=a;b<=D;b++)for(int c=b;c<=D;c++)for(int d=c;d<=D;d++){
  int e=-a-b-c-d;if(e>=d&&e<=D)v.push_back({a,b,c,d,e});
 }
 long long target=5LL*D*D/3,qtarget=1LL*D*D*D*D,edges=0,trips=0,quads=0;
 int N=v.size();std::vector<std::vector<int>> adj(N);
 for(int i=0;i<N;i++)for(int j=i;j<N;j++)if(dot(v[i],v[j])==target){adj[i].push_back(j);edges++;}
 std::cerr<<"D "<<D<<" vectors "<<N<<" edges "<<edges<<"\n";
 for(int i=0;i<N;i++)for(int j:adj[i]){
  std::vector<int> common;
  std::set_intersection(adj[i].begin(),adj[i].end(),adj[j].begin(),adj[j].end(),std::back_inserter(common));
  for(int k:common){
   if(triple(v[i],v[j],v[k]))continue;
   trips++;
   if(solve_fourth){
    if(fourth_compatible_mod(v[i],v[j],v[k],D)){
     std::cout<<"{\"D\":"<<D<<",\"columns\":[";
     for(int jj=0;jj<3;jj++){int ix=jj==0?i:jj==1?j:k;if(jj)std::cout<<",";std::cout<<"[";for(int r=0;r<5;r++){if(r)std::cout<<",";std::cout<<v[ix][r];}std::cout<<"]";}
     std::cout<<"]}\n"<<std::flush;
    }
    continue;
   }
   for(int l:adj[k]){
    if(!std::binary_search(common.begin(),common.end(),l))continue;
    if(triple(v[i],v[j],v[l])||triple(v[i],v[k],v[l])||triple(v[j],v[k],v[l]))continue;
    quads++;
    if(quad(v[i],v[j],v[k],v[l])!=qtarget)continue;
    std::cout<<"{\"D\":"<<D<<",\"columns\":[";
    for(int jj=0;jj<4;jj++){int ix=jj==0?i:jj==1?j:jj==2?k:l;if(jj)std::cout<<",";std::cout<<"[";for(int r=0;r<5;r++){if(r)std::cout<<",";std::cout<<v[ix][r];}std::cout<<"]";}
    std::cout<<"]}\n"<<std::flush;
   }
  }
 }
 std::cerr<<"D "<<D<<" triples "<<trips<<" four_cliques "<<quads<<"\n";
}
