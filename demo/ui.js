// page controls: the lighting toggle in the control row (moved out of index.html so that it runs after vortex.js)
(function () {
  const btn = document.getElementById('ltbtn'), a = document.getElementById('ltA'), b = document.getElementById('ltB');
  function show() { const sw = PROTO.light() === 'even';
    a.classList.toggle('on', !sw); b.classList.toggle('on', sw);
    btn.title = (sw ? 'lighting: even, a large even dome around the camera, so the swirls show everywhere'
                    : 'lighting: reference, the dim room of the 18,000 fps reference frames') + '. Drawing only. Click or press L to switch.'; }
  function flip() { PROTO.light(PROTO.light() === 'even' ? 'ref' : 'even'); show(); }
  btn.addEventListener('click', ev => { ev.stopPropagation(); flip(); });
  document.addEventListener('keydown', ev => { if ((ev.key === 'l' || ev.key === 'L') && !ev.metaKey && !ev.ctrlKey && !ev.altKey) { ev.preventDefault(); flip(); } });
  show();
})();
