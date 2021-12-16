https://dashadower.github.io

## Setup order

1. Fork barryclark/jekyll-now
2. fork한 리포 Git clone 
3. gem/jekyll 설치
4. jekyll-now의 index페이지는 블로그 페이지(/blog)의 형태로 되어있음. 처음 사이트에 접속했을때 표시되는 페이지는 블로그 글들이 아닌 introduction, about me페이지임. 그러므로 `index.md`파일을 수정해야함.
5. `index.md`의 layout를 page로 변경후, 소개글 작성
6. 이제 상단의 네이게이션 바에서 about 버튼을 삭제하고, 홈 버튼을 클릭시 index.md로 연결되게끔 수정이 필요함.
7. `_layouts/default.html`에서
   ```
   <nav>
     <a href="{{ site.baseurl }}/blog">Blog</a>
     <a href="{{ site.baseurl }}/">About</a>
   </nav>
   ```
    로 코드 수정. `{{site.baseurl}}`이 홈 화면이자 소개 페이지임.
8. resume.md파일을 생성후, `layout`를 default, `permalink`를 `/resume/`로 설정. resume 내용 작성후 저장.
9. 로컬에서 `bundle`
