---
layout: post
title: Solving code-server service failing to start after installation
usemathjax: true
---

After installing `code-server` through the installation script, systemctl can fail to start `code-server.service`:

```
$ systemctl status code-server@USER.service 
× code-server@USER.service - code-server
     Loaded: loaded (/usr/lib/systemd/system/code-server@.service; enabled; preset: enabled)
     Active: failed (Result: exit-code) since Thu 2025-02-13 10:58:16 UTC; 32s ago
    Process: 847 ExecStart=/usr/bin/code-server (code=exited, status=217/USER)
   Main PID: 847 (code=exited, status=217/USER)
        CPU: 7ms

Feb 13 10:58:16 ubuntu-s-1vcpu-1gb-sgp1-01 systemd[1]: code-server@USER.service: Scheduled restart job, restart >
Feb 13 10:58:16 ubuntu-s-1vcpu-1gb-sgp1-01 systemd[1]: code-server@USER.service: Start request repeated too quic>
Feb 13 10:58:16 ubuntu-s-1vcpu-1gb-sgp1-01 systemd[1]: code-server@USER.service: Failed with result 'exit-code'.
Feb 13 10:58:16 ubuntu-s-1vcpu-1gb-sgp1-01 systemd[1]: Failed to start code-server@USER.service - code-server.
```

The fix for me was to edit the service file's

```
User=%i
```

to 

```
User=root
```

or whatever your username is.
