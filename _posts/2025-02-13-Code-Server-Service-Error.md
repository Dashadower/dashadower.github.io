---
layout: post
title: Solving Issue of code-server service not starting after installation
usemathjax: true
---

After installing `code-server` through the installation script, systemctl can fail to start `code-server.service`. The fix for me was to edit the service file's

```
User=%i
```

to 

```
User=root
```

or whatever your username is.