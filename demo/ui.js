// v5.8 page controls (moved out of index.html so that it runs after vortex.js, which now loads after ve_core.wasm)
(function () {
  const mode = document.getElementById('ltmode'), a = document.getElementById('ltA'), b = document.getElementById('ltB');
  function show() { const sw = PROTO.light() === 'even';
    a.classList.toggle('on', !sw); b.classList.toggle('on', sw);
    mode.innerHTML = sw ? 'Even diffuse<small>a large even dome around the camera: the swirls show everywhere</small>' : 'Reference<small>the dim room of the 18,000 fps frames (v5.0)</small>'; }
  function flip() { PROTO.light(PROTO.light() === 'even' ? 'ref' : 'even'); show(); }
  document.getElementById('ltbtn').addEventListener('click', ev => { ev.stopPropagation(); flip(); });
  document.addEventListener('keydown', ev => { if ((ev.key === 'l' || ev.key === 'L') && !ev.metaKey && !ev.ctrlKey && !ev.altKey) { ev.preventDefault(); flip(); } });
  show();
})();
